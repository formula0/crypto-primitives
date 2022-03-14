use crate::crh::TwoToOneCRHSchemeGadget;
use crate::mmr::{Config, IdentityDigestConverter, VecDeque, get_peaks, take_while_vec, pos_height_in_tree, parent_offset, sibling_offset};
use crate::{CRHSchemeGadget, MMRPath};
use crate::mmr::error::{Result as MMRResult, Error as MMRError};

use ark_ff::Field;
use ark_ff::prelude::*;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::uint64::UInt64;

#[allow(unused)]
use ark_r1cs_std::prelude::*;
use ark_r1cs_std::ToBytesGadget;
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_std::borrow::Borrow;
use ark_std::fmt::Debug;
use ark_std::vec::Vec;

pub trait DigestVarConverter<From, To: ?Sized> {
    type TargetType: Borrow<To>;
    fn convert(from: From) -> Result<Self::TargetType, SynthesisError>;
}

impl<T> DigestVarConverter<T, T> for IdentityDigestConverter<T> {
    type TargetType = T;

    fn convert(from: T) -> Result<T, SynthesisError> {
        Ok(from)
    }
}

pub struct BytesVarDigestConverter<T: ToBytesGadget<ConstraintF>, ConstraintF: Field> {
    _prev_layer_digest: T,
    _constraint_field: ConstraintF,
}

impl<T: ToBytesGadget<ConstraintF>, ConstraintF: Field> DigestVarConverter<T, [UInt8<ConstraintF>]>
    for BytesVarDigestConverter<T, ConstraintF>
{
    type TargetType = Vec<UInt8<ConstraintF>>;

    fn convert(from: T) -> Result<Self::TargetType, SynthesisError> {
        from.to_non_unique_bytes()
    }
}

pub trait ConfigGadget<P: Config, ConstraintF: Field> {
    type Leaf: Debug + ?Sized;
    type LeafDigest: AllocVar<P::LeafDigest, ConstraintF>
        + EqGadget<ConstraintF>
        + ToBytesGadget<ConstraintF>
        + CondSelectGadget<ConstraintF>
        + R1CSVar<ConstraintF>
        + Debug
        + Clone
        + Sized;
    type LeafInnerConverter: DigestVarConverter<
        Self::LeafDigest,
        <Self::TwoToOneHash as TwoToOneCRHSchemeGadget<P::TwoToOneHash, ConstraintF>>::InputVar,
    >;
    type InnerDigest: AllocVar<P::InnerDigest, ConstraintF>
        + EqGadget<ConstraintF>
        + ToBytesGadget<ConstraintF>
        + CondSelectGadget<ConstraintF>
        + R1CSVar<ConstraintF>
        + Debug
        + Clone
        + Sized;

    type LeafHash: CRHSchemeGadget<
        P::LeafHash,
        ConstraintF,
        InputVar = Self::Leaf,
        OutputVar = Self::LeafDigest,
    >;
    type TwoToOneHash: TwoToOneCRHSchemeGadget<
        P::TwoToOneHash,
        ConstraintF,
        OutputVar = Self::InnerDigest,
    >;
}

type LeafParam<PG, P, ConstraintF> =
    <<PG as ConfigGadget<P, ConstraintF>>::LeafHash as CRHSchemeGadget<
        <P as Config>::LeafHash,
        ConstraintF,
    >>::ParametersVar;
type TwoToOneParam<PG, P, ConstraintF> =
    <<PG as ConfigGadget<P, ConstraintF>>::TwoToOneHash as TwoToOneCRHSchemeGadget<
        <P as Config>::TwoToOneHash,
        ConstraintF,
    >>::ParametersVar;

/// Represents a merkle tree path gadget.
#[derive(Debug, Derivative)]
#[derivative(Clone(bound = "P: Config, ConstraintF: Field, PG: ConfigGadget<P, ConstraintF>"))]
pub struct PathVar<P: Config, ConstraintF: Field, PG: ConfigGadget<P, ConstraintF>> {
    /// `path[i]` is 0 (false) iff ith non-leaf node from top to bottom is left.
    path: Vec<Boolean<ConstraintF>>,
    /// `auth_path[i]` is the entry of sibling of ith non-leaf node from top to bottom.
    auth_path: Vec<PG::InnerDigest>,
    
    mmr_size: UInt64<ConstraintF>,

    leaf_index: UInt64<ConstraintF>,
}

impl<P: Config, ConstraintF: Field, PG: ConfigGadget<P, ConstraintF>> AllocVar<MMRPath<P>, ConstraintF>
    for PathVar<P, ConstraintF, PG>
where
    P: Config,
    ConstraintF: Field,
{
    #[tracing::instrument(target = "r1cs", skip(cs, f))]
    fn new_variable<T: Borrow<MMRPath<P>>>(
        cs: impl Into<Namespace<ConstraintF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();
        f().and_then(|val| {
            let pos_list: Vec<_> = val.borrow().position_list().collect();
            let path = Vec::new_variable(
                ark_relations::ns!(cs, "path_bits"),
                || Ok(&pos_list[..(pos_list.len() - 1)]),
                mode,
            )?;
            let auth_path = Vec::new_variable(
                ark_relations::ns!(cs, "auth_path_nodes"),
                || Ok(&val.borrow().auth_path[..]),
                mode,
            )?;
            let mmr_size = UInt64::new_variable(
                ark_relations::ns!(cs, "mmr_size"),
                || Ok(val.borrow().mmr_size),
                mode,
            )?;
            let leaf_index = UInt64::new_variable(
                ark_relations::ns!(cs, "leaf_index"),
                || Ok(val.borrow().leaf_index),
                mode,
            )?;
            Ok(PathVar {
                path,
                auth_path,
                mmr_size,
                leaf_index
            })
        })
    }
}

impl<P: Config, ConstraintF: Field, PG: ConfigGadget<P, ConstraintF>> PathVar<P, ConstraintF, PG> {

    /// Check that hashing a Merkle mountain range path according to `self`, and
    /// with `leaf` as the leaf, leads to a Merkle mountain range root equalling `root`.
    #[tracing::instrument(target = "r1cs", skip(self, leaf_params, two_to_one_params))]
    pub fn verify_membership(
        &self,
        leaf_params: &LeafParam<PG, P, ConstraintF>,
        two_to_one_params: &TwoToOneParam<PG, P, ConstraintF>,
        root: &PG::InnerDigest,
        leaf: &PG::Leaf,
    ) -> Result<Boolean<ConstraintF>, SynthesisError> {
        let expected_root = self.calculate_root(leaf_params, two_to_one_params, leaf).unwrap();
        Ok(expected_root.is_eq(root)?)
    }

    /// Calculate the root of the Merkle tree assuming that `leaf` is the leaf on the path defined by `self`.
    #[tracing::instrument(target = "r1cs", skip(self, leaf_params, two_to_one_params))]
    pub fn calculate_root(
        &self,
        leaf_params: &LeafParam<PG, P, ConstraintF>,
        two_to_one_params: &TwoToOneParam<PG, P, ConstraintF>,
        leaf: &PG::Leaf,
    ) -> MMRResult<PG::InnerDigest> {
        let claimed_leaf_hash = PG::LeafHash::evaluate(leaf_params, leaf).unwrap();
        let converted_leaf_hash = PG::LeafInnerConverter::convert(claimed_leaf_hash).unwrap();

        let peak_hashes = self.calculate_peaks_hashes(two_to_one_params, &converted_leaf_hash).unwrap();
        Self::bagging_peaks_hashes(two_to_one_params, peak_hashes)
    }

    pub fn calculate_peaks_hashes(
        &self, 
        two_to_one_params: &TwoToOneParam<PG, P, ConstraintF>,
        converted_leaf_hash: &PG::InnerDigest,
    ) -> MMRResult<Vec<PG::InnerDigest>> {
        // special handle the only 1 leaf MMR
        if self.mmr_size.value().unwrap() == 1 && self.auth_path.len() == 1 {
            return Ok(vec![converted_leaf_hash.clone()]);
        }

        let path_iter = self.auth_path.iter();
        let peaks = get_peaks(self.mmr_size.value().unwrap());    
        let leaves = vec![(self.leaf_index.value().unwrap(), converted_leaf_hash.clone())];
        let mut peaks_hashes: Vec<PG::InnerDigest> = Vec::with_capacity(peaks.len() + 1);
        for peak_pos in peaks {
            let mut leaves: Vec<_> = take_while_vec(&mut leaves,|(pos, _)| *pos <= peak_pos);
            let peak_root = if leaves.len() == 1 && leaves[0].0 == peak_pos {
                // leaf is the peak
                leaves.remove(0).1
            } else if leaves.is_empty() {
                // if empty, means the next proof is a peak root or rhs bagged root
                if let Some(peak_root) = path_iter.next() {
                    peak_root.clone()
                } else {
                    // means that either all right peaks are bagged, or proof is corrupted
                    // so we break loop and check no items left
                    break;
                }
            } else {
                let peak_result = Self::calculate_peak_root(two_to_one_params, leaves, peak_pos, &mut path_iter).unwrap();
                peak_result
            };

            peaks_hashes.push(peak_root.clone());
        }
    
        // ensure nothing left in leaves
        if !leaves.is_empty() {
            return Err(MMRError::CorruptedProof);
        }
    
        // check rhs peaks
        if let Some(rhs_peaks_hashes) = path_iter.next() {
            peaks_hashes.push(rhs_peaks_hashes.clone());
        }
        // ensure nothing left in path_iter
        if path_iter.next().is_some() {
            return Err(MMRError::CorruptedProof);
        }
        Ok(peaks_hashes)
    }

    pub fn calculate_peak_root(
        two_to_one_params: &TwoToOneParam<PG, P, ConstraintF>,
        leaves: Vec<(u64, PG::InnerDigest)>,
        peak_pos: u64,
        path_iter: &mut Iterator<Item = &PG::InnerDigest>,
    ) -> MMRResult<PG::InnerDigest> {
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
                path_iter.next().ok_or(MMRError::CorruptedProof)?.clone()
            };

            let parent_item: PG::InnerDigest = if next_height > height {
                PG::TwoToOneHash::compress(two_to_one_params, &sibling_item, &item).unwrap()
            } else {
                PG::TwoToOneHash::compress(two_to_one_params, &item, &sibling_item).unwrap()
            };

            if parent_pos < peak_pos {
                queue.push_back((parent_pos, parent_item, height + 1));
            } else {
                return Ok(parent_item);
            }
        }
        Err(MMRError::CorruptedProof)
    }

    pub fn bagging_peaks_hashes(
        two_to_one_params: &TwoToOneParam<PG, P, ConstraintF>,
        mut peaks_hashes: Vec<PG::InnerDigest>,
    ) -> MMRResult<PG::InnerDigest> {
        // bagging peaks
        // bagging from right to left via hash(right, left).
        while peaks_hashes.len() > 1 {
            let right_peak = peaks_hashes.pop().expect("pop");
            let left_peak = peaks_hashes.pop().expect("pop");
            peaks_hashes.push(PG::TwoToOneHash::compress(two_to_one_params, &right_peak, &left_peak).unwrap());
        }
        peaks_hashes.pop().ok_or(MMRError::CorruptedProof)
    }
}


