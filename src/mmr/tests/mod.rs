#[cfg(feature = "r1cs")]
mod constraints;
mod test_utils;

mod bytes_mt_tests {

    use crate::{
        crh::{pedersen, *},
        mmr::*,
    };
    use ark_ed_on_bls12_381::EdwardsProjective as JubJub;
    use ark_ff::BigInteger256;
    use ark_std::{test_rng, UniformRand};

    #[derive(Clone)]
    pub(super) struct Window4x256;
    impl pedersen::Window for Window4x256 {
        const WINDOW_SIZE: usize = 4;
        const NUM_WINDOWS: usize = 256;
    }

    type LeafH = pedersen::CRH<JubJub, Window4x256>;
    type CompressH = pedersen::TwoToOneCRH<JubJub, Window4x256>;

    struct JubJubMerkleMountainRangeParams;

    impl Config for JubJubMerkleMountainRangeParams {
        type Leaf = [u8];

        type LeafDigest = <LeafH as CRHScheme>::Output;
        type LeafInnerDigestConverter = ByteDigestConverter<Self::LeafDigest>;
        type InnerDigest = <CompressH as TwoToOneCRHScheme>::Output;

        type LeafHash = LeafH;
        type TwoToOneHash = CompressH;
    }

    type JubJubMerkleMountainRange = MerkleMountainRange<JubJubMerkleMountainRangeParams>;

    /// Pedersen only takes bytes as leaf, so we use `ToBytes` trait.
    fn mmr_test<L: CanonicalSerialize>(leaves: &[L]) -> () {
        let mut rng = ark_std::test_rng();
        let leaves: Vec<_> = leaves
            .iter()
            .map(|leaf| crate::to_unchecked_bytes!(leaf).unwrap())
            .collect();
        let leaf_crh_params = <LeafH as CRHScheme>::setup(&mut rng).unwrap();
        let two_to_one_params = <CompressH as TwoToOneCRHScheme>::setup(&mut rng)
            .unwrap()
            .clone();
        let mut mmr = JubJubMerkleMountainRange::new(
            &leaf_crh_params.clone(),
            &two_to_one_params.clone(),
        );
        mmr.push_vec(leaves.iter().map(|x| x.as_slice())).expect("push error");
        let root = mmr.get_root().unwrap();
        // test merkle tree functionality without update
        for (i, leaf) in leaves.iter().enumerate() {
            let proof = mmr.generate_proof(i as u64).unwrap();
            assert!(proof
                .verify(&leaf_crh_params, &two_to_one_params, &root, leaf.as_slice())
                .unwrap());
        }
    }

    #[test]
    fn good_root_test() {
        let mut rng = test_rng();

        let mut leaves = Vec::new();
        for _ in 0..2u8 {
            leaves.push(BigInteger256::rand(&mut rng));
        }
        mmr_test(&leaves);

        let mut leaves = Vec::new();
        for _ in 0..4u8 {
            leaves.push(BigInteger256::rand(&mut rng));
        }
        mmr_test(&leaves);

        let mut leaves = Vec::new();
        for _ in 0..128u8 {
            leaves.push(BigInteger256::rand(&mut rng));
        }
        mmr_test(&leaves);
    }
}

mod field_mt_tests {
    use crate::crh::poseidon;
    use crate::mmr::tests::test_utils::poseidon_parameters;
    use crate::mmr::{Config, IdentityDigestConverter};
    use crate::MerkleMountainRange;
    use ark_std::{test_rng, One, UniformRand};

    type F = ark_ed_on_bls12_381::Fr;
    type H = poseidon::CRH<F>;
    type TwoToOneH = poseidon::TwoToOneCRH<F>;

    struct FieldMTConfig;
    impl Config for FieldMTConfig {
        type Leaf = [F];
        type LeafDigest = F;
        type LeafInnerDigestConverter = IdentityDigestConverter<F>;
        type InnerDigest = F;
        type LeafHash = H;
        type TwoToOneHash = TwoToOneH;
    }

    type FieldMT = MerkleMountainRange<FieldMTConfig>;

    fn mmr_test(leaves: &[Vec<F>]) -> () {
        let leaves = leaves.to_vec();
        let leaf_crh_params = poseidon_parameters();
        let two_to_one_params = leaf_crh_params.clone();

        let mut mmr = FieldMT::new(
            &leaf_crh_params,
            &two_to_one_params,
        );

        mmr.push_vec(leaves.iter().map(|x| x.as_slice())).expect("push error");

        let root = mmr.get_root().unwrap();

        // test merkle tree functionality without update
        for (i, leaf) in leaves.iter().enumerate() {
            let proof = mmr.generate_proof(i as u64).unwrap();
            assert!(proof
                .verify(&leaf_crh_params, &two_to_one_params, &root, leaf.as_slice())
                .unwrap());
        }

        {
            // wrong root should lead to error but do not panic
            let wrong_root = root + F::one();
            let proof = mmr.generate_proof(0).unwrap();
            assert!(!proof
                .verify(
                    &leaf_crh_params,
                    &two_to_one_params,
                    &wrong_root,
                    leaves[0].as_slice()
                )
                .unwrap())
        }
    }

    #[test]
    fn good_root_test() {
        let mut rng = test_rng();
        let mut rand_leaves = || (0..3).map(|_| F::rand(&mut rng)).collect();

        let mut leaves: Vec<Vec<_>> = Vec::new();
        for _ in 0..128u8 {
            leaves.push(rand_leaves())
        }
        mmr_test(&leaves);
    }
}
