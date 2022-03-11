#![allow(clippy::needless_range_loop)]

/// Defines a trait to chain two types of CRHs.
use crate::crh::TwoToOneCRHScheme;
use crate::{CRHScheme, Error};

use ark_ff::ToBytes;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Write};
use ark_std::borrow::{Borrow, Cow};
use ark_std::hash::Hash;
use ark_std::vec::Vec;
use ark_std::collections::VecDeque;

mod error;
mod mmr_store;

use mmr_store::{MMRBatch, MMRStore};


#[cfg(test)]
mod tests;

#[cfg(feature = "r1cs")]
pub mod constraints;

/// Convert the hash digest in different layers by converting previous layer's output to
/// `TargetType`, which is a `Borrow` to next layer's input.
pub trait DigestConverter<From, To: ?Sized> {
    type TargetType: Borrow<To>;
    fn convert(item: From) -> Result<Self::TargetType, Error>;
}

/// A trivial converter where digest of previous layer's hash is the same as next layer's input.
pub struct IdentityDigestConverter<T> {
    _prev_layer_digest: T,
}

impl<T> DigestConverter<T, T> for IdentityDigestConverter<T> {
    type TargetType = T;
    fn convert(item: T) -> Result<T, Error> {
        Ok(item)
    }
}

/// Convert previous layer's digest to bytes and use bytes as input for next layer's digest.
/// TODO: `ToBytes` trait will be deprecated in future versions.
pub struct ByteDigestConverter<T: CanonicalSerialize + ToBytes> {
    _prev_layer_digest: T,
}

impl<T: CanonicalSerialize + ToBytes> DigestConverter<T, [u8]> for ByteDigestConverter<T> {
    type TargetType = Vec<u8>;

    fn convert(item: T) -> Result<Self::TargetType, Error> {
        // TODO: In some tests, `serialize` is not consistent with constraints. Try fix those.
        Ok(crate::to_unchecked_bytes!(item)?)
    }
}

/// Merkle tree have three types of hashes.
/// * `LeafHash`: Convert leaf to leaf digest
/// * `TwoLeavesToOneHash`: Convert two leaf digests to one inner digest. This one can be a wrapped
/// version `TwoHashesToOneHash`, which first converts leaf digest to inner digest.
/// * `TwoHashesToOneHash`: Compress two inner digests to one inner digest
pub trait Config {
    type Leaf: ?Sized; // merkle tree does not store the leaf
                       // leaf layer
    type LeafDigest: ToBytes
        + PartialEq
        + Clone
        + Eq
        + core::fmt::Debug
        + Hash
        + Default
        + CanonicalSerialize
        + CanonicalDeserialize;
    // transition between leaf layer to inner layer
    type LeafInnerDigestConverter: DigestConverter<
        Self::LeafDigest,
        <Self::TwoToOneHash as TwoToOneCRHScheme>::Input,
    >;
    // inner layer
    type InnerDigest: ToBytes
        + PartialEq
        + Clone
        + Eq
        + core::fmt::Debug
        + Hash
        + Default
        + CanonicalSerialize
        + CanonicalDeserialize;

    // Tom's Note: in the future, if we want different hash function, we can simply add more
    // types of digest here and specify a digest converter. Same for constraints.

    /// leaf -> leaf digest
    /// If leaf hash digest and inner hash digest are different, we can create a new
    /// leaf hash which wraps the original leaf hash and convert its output to `Digest`.
    type LeafHash: CRHScheme<Input = Self::Leaf, Output = Self::LeafDigest>;
    /// 2 inner digest -> inner digest
    type TwoToOneHash: TwoToOneCRHScheme<Output = Self::InnerDigest>;
}

pub type TwoToOneParam<P> = <<P as Config>::TwoToOneHash as TwoToOneCRHScheme>::Parameters;
pub type LeafParam<P> = <<P as Config>::LeafHash as CRHScheme>::Parameters;

/// Stores the hashes of a particular path (in order) from root to leaf.
/// For example:
/// ```tree_diagram
///         [A]
///        /   \
///      [B]    C
///     / \   /  \
///    D [E] F    H
///   .. / \ ....
///    [I] J
/// ```
///  Suppose we want to prove I, then `leaf_sibling_hash` is J, `auth_path` is `[C,D]`
#[derive(Derivative, CanonicalSerialize, CanonicalDeserialize)]
#[derivative(
    Clone(bound = "P: Config"),
    Debug(bound = "P: Config"),
    Default(bound = "P: Config")
)]
pub struct Path<P: Config> {
    pub auth_path: Vec<P::InnerDigest>,

    pub leaf_index: usize,

    pub mmr_size: usize,
}

impl<P: Config> Path<P> {
    /// The position of on_path node in `leaf_and_sibling_hash` and `non_leaf_and_sibling_hash_path`.
    /// `position[i]` is 0 (false) iff `i`th on-path node from top to bottom is on the left.
    ///
    /// This function simply converts `self.leaf_index` to boolean array in big endian form.
    #[allow(unused)] // this function is actually used when r1cs feature is on
    fn position_list(&'_ self) -> impl '_ + Iterator<Item = bool> {
        (0..self.auth_path.len() + 1)
            .map(move |i| ((self.leaf_index >> i) & 1) != 0)
            .rev()
    }
}

impl<P: Config> Path<P> {
    /// Verify that a leaf is at `self.index` of the merkle tree.
    /// * `leaf_size`: leaf size in number of bytes

    pub fn verify(&self,
        leaf_hash_params: &LeafParam<P>,
        two_to_one_params: &TwoToOneParam<P>,
        root_hash: &P::InnerDigest,
        leaf: L,
    ) -> Result<bool> {

        let claimed_leaf_hash = P::LeafHash::evaluate(&leaf_hash_params, leaf)?;
        let converted_leaf_hash = P::LeafInnerDigestConverter::convert(claimed_leaf_hash)?;

        let leaves = vec![(self.leaf_index, converted_leaf_hash)];

        self.calculate_root(leaves, two_to_one_params)
            .map(|calculated_root| calculated_root == root)
    }

    pub fn calculate_root(&self, 
        leaves: Vec<(u64, MMRDigest)>,
        two_to_one_params: &TwoToOneParam<P>,
    ) -> Result<MMRDigest> {
        calculate_root::<_, _>(leaves, self.mmr_size, self.path.iter(), two_to_one_params)
    }

}


/// merkle proof
/// 1. sort items by position
/// 2. calculate root of each peak
/// 3. bagging peaks
fn calculate_root<
    'a,
    T: 'a + MMRDigest,
    I: Iterator<Item = &'a T>,
>(
    leaves: Vec<(usize, T)>,
    mmr_size: usize,
    path_iter: I,
    two_to_one_params: &TwoToOneParam<P>,
) -> Result<T> {
    let peaks_hashes = calculate_peaks_hashes::<_, _>(leaves, mmr_size, path_iter, two_to_one_params.clone())?;
    bagging_peaks_hashes::<_>(peaks_hashes, two_to_one_params)
}

fn calculate_peaks_hashes<
    'a,
    T: 'a + MMRDigest,
    I: Iterator<Item = &'a T>,
>(
    mut leaves: Vec<(usize, T)>,
    mmr_size: usize,
    mut proof_iter: I,
    two_to_one_params: &TwoToOneParam<P>,
) -> Result<Vec<T>> {
    // special handle the only 1 leaf MMR
    if mmr_size == 1 && leaves.len() == 1 && leaves[0].0 == 0 {
        return Ok(leaves.into_iter().map(|(_pos, item)| item).collect());
    }
    // sort items by position
    leaves.sort_by_key(|(pos, _)| *pos);
    let peaks = get_peaks(mmr_size);

    let mut peaks_hashes: Vec<T> = Vec::with_capacity(peaks.len() + 1);
    for peak_pos in peaks {
        let mut leaves: Vec<_> = take_while_vec(&mut leaves, |(pos, _)| *pos <= peak_pos);
        let peak_root = if leaves.len() == 1 && leaves[0].0 == peak_pos {
            // leaf is the peak
            leaves.remove(0).1
        } else if leaves.is_empty() {
            // if empty, means the next proof is a peak root or rhs bagged root
            if let Some(peak_root) = proof_iter.next() {
                peak_root.clone()
            } else {
                // means that either all right peaks are bagged, or proof is corrupted
                // so we break loop and check no items left
                break;
            }
        } else {
            calculate_peak_root::<_, _>(leaves, peak_pos, &mut proof_iter, two_to_one_params)?
        };
        peaks_hashes.push(peak_root.clone());
    }

    // ensure nothing left in leaves
    if !leaves.is_empty() {
        return Err(Error::CorruptedProof);
    }

    // check rhs peaks
    if let Some(rhs_peaks_hashes) = proof_iter.next() {
        peaks_hashes.push(rhs_peaks_hashes.clone());
    }
    // ensure nothing left in proof_iter
    if proof_iter.next().is_some() {
        return Err(Error::CorruptedProof);
    }
    Ok(peaks_hashes)
}

fn calculate_peak_root<
    'a,
    T: 'a + MMRDigest,
    I: Iterator<Item = &'a T>,
>(
    leaves: Vec<(u64, T)>,
    peak_pos: usize,
    path_iter: &mut I,
    two_to_one_params: &TwoToOneParam<P>,
) -> Result<T> {
    debug_assert!(!leaves.is_empty(), "can't be empty");
    // (position, hash, height)
    let mut queue: VecDeque<_> = leaves
        .into_iter()
        .map(|(pos, item)| (pos, item, 0u32))
        .collect();

    // calculate tree root from each items
    while let Some((pos, item, height)) = queue.pop_front() {
        if pos == peak_pos {
            // return root
            return Ok(item);
        }
        // calculate sibling
        let next_height = pos_height_in_tree(pos + 1);
        let (sib_pos, parent_pos) = {
            let sibling_offset = sibling_offset(height);
            if next_height > height {
                // implies pos is right sibling
                (pos - sibling_offset, pos + 1)
            } else {
                // pos is left sibling
                (pos + sibling_offset, pos + parent_offset(height))
            }
        };
        let sibling_item = if Some(&sib_pos) == queue.front().map(|(pos, _, _)| pos) {
            queue.pop_front().map(|(_, item, _)| item).unwrap()
        } else {
            proof_iter.next().ok_or(Error::CorruptedProof)?.clone()
        };

        let parent_item = if next_height > height {
            P::TwoToOneHash::compress(
                two_to_one_hash_param.clone(),
                &sibling_item.clone(),
                &item.clone()
            );
        } else {
            P::TwoToOneHash::compress(
                two_to_one_hash_param.clone(),
                &item.clone(),
                &sibling_item.clone()
            );
        };

        if parent_pos < peak_pos {
            queue.push_back((parent_pos, parent_item, height + 1));
        } else {
            return Ok(parent_item);
        }
    }
    Err(Error::CorruptedProof)
}

fn bagging_peaks_hashes<'a, T: 'a + MMRDigest>(
    mut peaks_hashes: Vec<T>,
    two_to_one_params: &TwoToOneParam<P>,
) -> Result<T> {
    // bagging peaks
    // bagging from right to left via hash(right, left).
    while peaks_hashes.len() > 1 {
        let right_peak = peaks_hashes.pop().expect("pop");
        let left_peak = peaks_hashes.pop().expect("pop");
        peaks_hashes.push(
            P::TwoToOneHash::compress(
                two_to_one_hash_param.clone(),
                &right_peak.clone(), 
                &left_peak.clone()
            )
        );
    }
    peaks_hashes.pop().ok_or(Error::CorruptedProof)
}

fn take_while_vec<MMRDigest, P: Fn(&MMRDigest) -> bool>(v: &mut Vec<MMRDigest>, p: P) -> Vec<MMRDigest> {
    for i in 0..v.len() {
        if !p(&v[i]) {
            return v.drain(..i).collect();
        }
    }
    v.drain(..).collect()
}





/// Defines a merkle mountain range data structure.
/// This merkle mountain range has runtime fixed height, and assumes number of leaves is 2^height.
///
/// TODO: add RFC-6962 compatible merkle mountain range in the future.
/// For this release, padding will not be supported because of security concerns: if the leaf hash and two to one hash uses same underlying
/// CRH, a malicious prover can prove a leaf while the actual node is an inner node. In the future, we can prefix leaf hashes in different layers to
/// solve the problem.
#[derive(Derivative)]
#[derivative(Clone(bound = "P: Config"))]

type MMRDigest = P::InnerDigest + P::LeaftDigest;

pub struct MerkleMountainRange<P: Config> {
    /// Store leaf and inner digests
    batch: MMRBatch<MMRDigest, MMRStore<MMRDigest>>,
    /// Store the inner hash parameters
    two_to_one_hash_param: TwoToOneParam<P>,
    /// Store the leaf hash parameters
    leaf_hash_param: LeafParam<P>,
    /// Stores the size of the MerkleMountainRange
    mmr_size: usize,
}

impl<P: Config> MerkleMountainRange<P> {

    /// Returns a new merkle mountain range. 
    pub fn new<L: Borrow<P::Leaf>>(
        leaf_hash_param: &LeafParam<P>,
        two_to_one_hash_param: &TwoToOneParam<P>,
    ) -> Self {
        MerkleMountainRange {
            batch: MMRBatch::new(store),
            two_to_one_hash_param: two_to_one_hash_param.clone(),
            leaf_hash_param: leaf_hash_param.clone(),
            mmr_size: 0,
        }
    }

    // find internal MMR elem, the pos must exists, otherwise a error will return
    fn find_elem<'b>(&self, pos: usize, hashes: &'b [MMRDigest]) -> Result<Cow<'b, MMRDigest>> {
        let pos_offset = pos.checked_sub(self.mmr_size);
        if let Some(elem) = pos_offset.and_then(|i| hashes.get(i as usize)) {
            return Ok(Cow::Borrowed(elem));
        }
        let elem = self.batch.get_elem(pos)?.ok_or(Error::InconsistentStore)?;
        Ok(Cow::Owned(elem))
    }

    // push a element and return position
    pub fn push(&mut self, elem: MMRDigest) -> Result<usize> {
        let mut elems: Vec<MMRDigest> = Vec::new();
        // position of new elem
        let elem_pos = self.mmr_size;
        elems.push(elem);
        let mut height = 0usize;
        let mut pos = elem_pos;
        // continue to merge tree node if next pos heigher than current
        while pos_height_in_tree(pos + 1) > height {
            pos += 1;
            let left_pos = pos - parent_offset(height);
            let right_pos = left_pos + sibling_offset(height);
            let mut left_elem = *self.find_elem(left_pos, &elems)?;
            let mut right_elem = *self.find_elem(right_pos, &elems)?;

            if pos_height_in_tree(pos + 1) == 2 {
                left_elem = P::LeafInnerDigestConverter::convert(left_elem);
                right_elem = P::LeafInnerDigestConverter::convert(right_elem);
            }

            let parent_elem = P::TwoToOneHash::compress(
                self.two_to_one_hash_param.clone(),
                left_elem.clone(), 
                right_elem.clone()
            );

            elems.push(parent_elem);
            height += 1
        }
        // store hashes
        self.batch.append(elem_pos, elems);
        // update mmr_size
        self.mmr_size = pos + 1;
        Ok(elem_pos)
    }

    /// Returns the root of the Merkle Mount Range.
    pub fn get_root(&self) -> MMRDigest {
        if self.mmr_size == 0 {
            return Err(Error::GetRootOnEmpty);
        } else if self.mmr_size == 1 {
            return self.batch.get_elem(0)?.ok_or(Error::InconsistentStore);
        }
        let peaks: Vec<MMRDigest> = get_peaks(self.mmr_size)
            .into_iter()
            .map(|peak_pos| {
                self.batch
                    .get_elem(peak_pos)
                    .and_then(|elem| elem.ok_or(Error::InconsistentStore))
            })
            .collect::<Result<Vec<MMRDigest>>>()?;
        self.bag_rhs_peaks(peaks)?.ok_or(Error::InconsistentStore)
    }

    pub fn bag_rhs_peaks(&self, mut rhs_peaks: Vec<MMRDigest>, two_to_one_hash_param: &TwoToOneParam<P>,) -> Result<Option<MMRDigest>> {
        while rhs_peaks.len() > 1 {
            let right_peak = rhs_peaks.pop().expect("pop");
            let left_peak = rhs_peaks.pop().expect("pop");
            rhs_peaks.push(
                P::TwoToOneHash::compress(
                    two_to_one_hash_param.clone(),
                    right_peak.clone(), 
                    left_peak.clone()
                )
            );
        }
        Ok(rhs_peaks.pop())
    }

    /// Returns the height of the Merkle tree.
    pub fn mmr_size(&self) -> usize {
        self.mmr_size
    }

    pub fn is_empty(&self) -> bool {
        self.mmr_size == 0
    }

    /// Returns the authentication path from leaf at `index` to root.
    pub fn generate_proof(&self, index: usize) -> Result<Path<P>, crate::Error> {
        if self.mmr_size == 1 && index == 0 {
            return Ok(
                Path{
                    leaf_index: index,
                    auth_path: Vec::new(),
                });
        }

        let mut pos_list = vec![index];

        let peaks = get_peaks(self.mmr_size);
        let mut path: Vec<MMRDigest> = Vec::new();

        let mut bagging_track = 0;
        for peak_pos in peaks {
            let pos_list: Vec<_> = take_while_vec(&mut pos_list, |&pos| pos <= peak_pos);
            if pos_list.is_empty() {
                bagging_track += 1;
            } else {
                bagging_track = 0;
            }
            self.gen_proof_for_peak(&mut proof, pos_list, peak_pos)?;
        }

        if bagging_track > 1 {
            let rhs_peaks = path.split_off(path.len() - bagging_track);
            path.push(self.bag_rhs_peaks(rhs_peaks)?.expect("bagging rhs peaks"));
        }

        Ok(Path {
            leaf_index: index,
            auth_path: path,
            mmr_size: self.mmr_size
        })
    }
}

// helper

pub fn leaf_index_to_pos(index: usize) -> usize {
    // mmr_size - H - 1, H is the height(intervals) of last peak
    leaf_index_to_mmr_size(index) - (index + 1).trailing_zeros() as usize - 1
}

pub fn leaf_index_to_mmr_size(index: usize) -> usize {
    // leaf index start with 0
    let leaves_count = index + 1;

    // the peak count(k) is actually the count of 1 in leaves count's binary representation
    let peak_count = leaves_count.count_ones() as usize;

    2 * leaves_count - peak_count
}

pub fn pos_height_in_tree(mut pos: usize) -> usize {
    pos += 1;
    fn all_ones(num: usize) -> bool {
        num != 0 && num.count_zeros() == num.leading_zeros()
    }
    fn jump_left(pos: usize) -> usize {
        let bit_length = 64 - pos.leading_zeros();
        let most_significant_bits = 1 << (bit_length - 1);
        pos - (most_significant_bits - 1)
    }

    while !all_ones(pos) {
        pos = jump_left(pos)
    }

    64 - pos.leading_zeros() - 1
}

pub fn parent_offset(height: usize) -> usize {
    2 << height
}

pub fn sibling_offset(height: usize) -> usize {
    (2 << height) - 1
}

pub fn get_peaks(mmr_size: usize) -> Vec<P::InnerDigest> {
    let mut pos_s = Vec::new();
    let (mut height, mut pos) = left_peak_height_pos(mmr_size);
    pos_s.push(pos);
    while height > 0 {
        let peak = match get_right_peak(height, pos, mmr_size) {
            Some(peak) => peak,
            None => break,
        };
        height = peak.0;
        pos = peak.1;
        pos_s.push(pos);
    }
    pos_s
}

fn get_right_peak(mut height: usize, mut pos: usize, mmr_size: usize) -> Option<(usize, usize)> {
    // move to right sibling pos
    pos += sibling_offset(height);
    // loop until we find a pos in mmr
    while pos > mmr_size - 1 {
        if height == 0 {
            return None;
        }
        // move to left child
        pos -= parent_offset(height - 1);
        height -= 1;
    }
    Some((height, pos))
}

fn get_peak_pos_by_height(height: usize) -> usize {
    (1 << (height + 1)) - 2
}

fn left_peak_height_pos(mmr_size: usize) -> (usize, usize) {
    let mut height = 1;
    let mut prev_pos = 0;
    let mut pos = get_peak_pos_by_height(height);
    while pos < mmr_size {
        height += 1;
        prev_pos = pos;
        pos = get_peak_pos_by_height(height);
    }
    (height - 1, prev_pos)
}
