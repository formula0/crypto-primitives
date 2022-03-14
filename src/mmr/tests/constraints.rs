mod byte_mt_tests {
    use crate::crh::{pedersen, TwoToOneCRHScheme, TwoToOneCRHSchemeGadget};

    use crate::mmr::constraints::{BytesVarDigestConverter, ConfigGadget};
    use crate::mmr::{ByteDigestConverter, Config};
    use crate::{CRHScheme, CRHSchemeGadget, MerkleMountainRange, PathVar};
    use ark_ed_on_bls12_381::{constraints::EdwardsVar, EdwardsProjective as JubJub, Fq};
    #[allow(unused)]
    use ark_r1cs_std::prelude::*;
    #[allow(unused)]
    use ark_relations::r1cs::ConstraintSystem;

    #[derive(Clone)]
    pub(super) struct Window4x256;
    impl pedersen::Window for Window4x256 {
        const WINDOW_SIZE: usize = 4;
        const NUM_WINDOWS: usize = 256;
    }

    type LeafH = pedersen::CRH<JubJub, Window4x256>;
    type LeafHG = pedersen::constraints::CRHGadget<JubJub, EdwardsVar, Window4x256>;

    type CompressH = pedersen::TwoToOneCRH<JubJub, Window4x256>;
    type CompressHG = pedersen::constraints::TwoToOneCRHGadget<JubJub, EdwardsVar, Window4x256>;

    type LeafVar<ConstraintF> = [UInt8<ConstraintF>];

    struct JubJubMerkleMountainRangeParams;

    impl Config for JubJubMerkleMountainRangeParams {
        type Leaf = [u8];
        type LeafDigest = <LeafH as CRHScheme>::Output;
        type LeafInnerDigestConverter = ByteDigestConverter<Self::LeafDigest>;

        type InnerDigest = <CompressH as TwoToOneCRHScheme>::Output;
        type LeafHash = LeafH;
        type TwoToOneHash = CompressH;
    }

    type ConstraintF = Fq;
    struct JubJubMerkleMountainRangeParamsVar;
    impl ConfigGadget<JubJubMerkleMountainRangeParams, ConstraintF> for JubJubMerkleMountainRangeParamsVar {
        type Leaf = LeafVar<ConstraintF>;
        type LeafDigest = <LeafHG as CRHSchemeGadget<LeafH, ConstraintF>>::OutputVar;
        type LeafInnerConverter = BytesVarDigestConverter<Self::LeafDigest, ConstraintF>;
        type InnerDigest =
            <CompressHG as TwoToOneCRHSchemeGadget<CompressH, ConstraintF>>::OutputVar;
        type LeafHash = LeafHG;
        type TwoToOneHash = CompressHG;
    }

    type JubJubMerkleMountainRange = MerkleMountainRange<JubJubMerkleMountainRangeParams>;

    /// Generate a merkle tree, its constraints, and test its constraints
    fn mmr_test(
        leaves: &[Vec<u8>],
        use_bad_root: bool,
        update_query: Option<(usize, Vec<u8>)>,
    ) -> () {
        let mut rng = ark_std::test_rng();

        let leaf_crh_params = <LeafH as CRHScheme>::setup(&mut rng).unwrap();
        let two_to_one_crh_params = <CompressH as TwoToOneCRHScheme>::setup(&mut rng).unwrap();
        let mut mmr = JubJubMerkleMountainRange::new(
            &leaf_crh_params,
            &two_to_one_crh_params,
        );

        mmr.push_vec(leaves.iter().map(|v| v.as_slice()));

        let root = mmr.get_root().unwrap;
        for (i, leaf) in leaves.iter().enumerate() {
            let cs = ConstraintSystem::<Fq>::new_ref();
            let proof = mmr.generate_proof(i).unwrap();
            assert!(proof
                .verify(
                    &leaf_crh_params,
                    &two_to_one_crh_params,
                    &root,
                    leaf.as_slice()
                )
                .unwrap());

            // Allocate Merkle Tree Root
            let root = <LeafHG as CRHSchemeGadget<LeafH, _>>::OutputVar::new_witness(
                ark_relations::ns!(cs, "new_digest"),
                || {
                    if use_bad_root {
                        Ok(<LeafH as CRHScheme>::Output::default())
                    } else {
                        Ok(root)
                    }
                },
            )
            .unwrap();

            let constraints_from_digest = cs.num_constraints();
            println!("constraints from digest: {}", constraints_from_digest);

            // Allocate Parameters for CRH
            let leaf_crh_params_var =
                <LeafHG as CRHSchemeGadget<LeafH, _>>::ParametersVar::new_constant(
                    ark_relations::ns!(cs, "leaf_crh_parameter"),
                    &leaf_crh_params,
                )
                .unwrap();
            let two_to_one_crh_params_var =
                <CompressHG as TwoToOneCRHSchemeGadget<CompressH, _>>::ParametersVar::new_constant(
                    ark_relations::ns!(cs, "two_to_one_crh_parameter"),
                    &two_to_one_crh_params,
                )
                .unwrap();

            let constraints_from_params = cs.num_constraints() - constraints_from_digest;
            println!("constraints from parameters: {}", constraints_from_params);

            // Allocate Leaf
            let leaf_g = UInt8::new_input_vec(cs.clone(), leaf).unwrap();

            let constraints_from_leaf =
                cs.num_constraints() - constraints_from_params - constraints_from_digest;
            println!("constraints from leaf: {}", constraints_from_leaf);

            // Allocate Merkle Tree Path
            let cw: PathVar<JubJubMerkleMountainRangeParams, Fq, JubJubMerkleMountainRangeParamsVar> =
                PathVar::new_witness(ark_relations::ns!(cs, "new_witness"), || Ok(&proof)).unwrap();

            let constraints_from_path = cs.num_constraints()
                - constraints_from_params
                - constraints_from_digest
                - constraints_from_leaf;
            println!("constraints from path: {}", constraints_from_path);

            assert!(cs.is_satisfied().unwrap());
            assert!(cw
                .verify_membership(
                    &leaf_crh_params_var,
                    &two_to_one_crh_params_var,
                    &root,
                    &leaf_g,
                )
                .unwrap()
                .value()
                .unwrap());
            let setup_constraints = constraints_from_leaf
                + constraints_from_digest
                + constraints_from_params
                + constraints_from_path;
            println!(
                "number of constraints: {}",
                cs.num_constraints() - setup_constraints
            );

            assert!(
                cs.is_satisfied().unwrap(),
                "verification constraints not satisfied"
            );
        }
    }

    #[test]
    fn good_root_test() {
        let mut leaves = Vec::new();
        for i in 0..4u8 {
            let input = vec![i; 30];
            leaves.push(input);
        }
        mmr_test(&leaves, false, Some((3usize, vec![7u8; 30])));
    }

    #[test]
    #[should_panic]
    fn bad_root_test() {
        let mut leaves = Vec::new();
        for i in 0..4u8 {
            let input = vec![i; 30];
            leaves.push(input);
        }
        mmr_test(&leaves, true, None);
    }
}

mod field_mt_tests {
    use crate::crh::{poseidon, TwoToOneCRHSchemeGadget};
    use crate::mmr::constraints::ConfigGadget;
    use crate::mmr::tests::test_utils::poseidon_parameters;
    use crate::mmr::{Config, IdentityDigestConverter};
    use crate::{CRHSchemeGadget, MerkleMountainRange, PathVar};
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::fields::fp::FpVar;
    use ark_r1cs_std::uint32::UInt32;
    use ark_r1cs_std::R1CSVar;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::{test_rng, One, UniformRand};

    type F = ark_ed_on_bls12_381::Fr;
    type H = poseidon::CRH<F>;
    type HG = poseidon::constraints::CRHGadget<F>;
    type TwoToOneH = poseidon::TwoToOneCRH<F>;
    type TwoToOneHG = poseidon::constraints::TwoToOneCRHGadget<F>;

    type LeafVar = [FpVar<F>];

    struct FieldMTConfig;
    impl Config for FieldMTConfig {
        type Leaf = [F];
        type LeafDigest = F;
        type LeafInnerDigestConverter = IdentityDigestConverter<F>;
        type InnerDigest = F;
        type LeafHash = H;
        type TwoToOneHash = TwoToOneH;
    }

    struct FieldMTConfigVar;

    impl ConfigGadget<FieldMTConfig, F> for FieldMTConfigVar {
        type Leaf = LeafVar;
        type LeafDigest = FpVar<F>;
        type LeafInnerConverter = IdentityDigestConverter<FpVar<F>>;
        type InnerDigest = FpVar<F>;
        type LeafHash = HG;
        type TwoToOneHash = TwoToOneHG;
    }

    type FieldMT = MerkleMountainRange<FieldMTConfig>;

    fn mmr_test(
        leaves: &[Vec<F>],
        use_bad_root: bool,
        update_query: Option<(usize, Vec<F>)>,
    ) {
        let leaf_crh_params = poseidon_parameters();
        let two_to_one_params = leaf_crh_params.clone();
        let mut mmr = FieldMT::new(
            &leaf_crh_params,
            &two_to_one_params,
        );

        mmr.push_vec(leaves.iter().map(|x| x.as_slice()));

        let root = mmr.get_root().unwrap();
        for (i, leaf) in leaves.iter().enumerate() {
            let cs = ConstraintSystem::<F>::new_ref();
            let proof = tree.generate_proof(i).unwrap();
            assert!(proof
                .verify(&leaf_crh_params, &two_to_one_params, &root, leaf.as_slice())
                .unwrap());
            // Allocate MT root
            let root = FpVar::new_witness(cs.clone(), || {
                if use_bad_root {
                    Ok(root + F::one())
                } else {
                    Ok(root)
                }
            })
            .unwrap();

            let constraints_from_digest = cs.num_constraints();
            println!("constraints from digest: {}", constraints_from_digest);

            let leaf_crh_params_var = <HG as CRHSchemeGadget<H, _>>::ParametersVar::new_constant(
                ark_relations::ns!(cs, "leaf_crh_params"),
                &leaf_crh_params,
            )
            .unwrap();

            let two_to_one_crh_params_var =
                <TwoToOneHG as TwoToOneCRHSchemeGadget<TwoToOneH, _>>::ParametersVar::new_constant(
                    ark_relations::ns!(cs, "two_to_one_params"),
                    &leaf_crh_params,
                )
                .unwrap();

            let constraints_from_params = cs.num_constraints() - constraints_from_digest;
            println!("constraints from parameters: {}", constraints_from_params);

            // Allocate Leaf
            let leaf_g: Vec<_> = leaf
                .iter()
                .map(|x| FpVar::new_input(cs.clone(), || Ok(*x)).unwrap())
                .collect();

            let constraints_from_leaf =
                cs.num_constraints() - constraints_from_params - constraints_from_digest;
            println!("constraints from leaf: {}", constraints_from_leaf);

            // Allocate MT Path
            let mut cw = PathVar::<FieldMTConfig, F, FieldMTConfigVar>::new_witness(
                ark_relations::ns!(cs, "new_witness"),
                || Ok(&proof),
            )
            .unwrap();

            let constraints_from_path = cs.num_constraints()
                - constraints_from_params
                - constraints_from_digest
                - constraints_from_leaf;
            println!("constraints from path: {}", constraints_from_path);
            assert!(cs.is_satisfied().unwrap());

            // try replace the path index
            let leaf_pos = UInt32::new_witness(cs.clone(), || Ok(i as u32))
                .unwrap()
                .to_bits_le();
            cw.set_leaf_position(leaf_pos.clone());

            // check if get_leaf_position is correct
            let expected_leaf_pos = leaf_pos.value().unwrap();
            let mut actual_leaf_pos = cw.get_leaf_position().value().unwrap();
            actual_leaf_pos.extend((0..(32 - actual_leaf_pos.len())).map(|_| false));
            assert_eq!(expected_leaf_pos, actual_leaf_pos);

            assert!(cw
                .verify_membership(
                    &leaf_crh_params_var,
                    &two_to_one_crh_params_var,
                    &root,
                    &leaf_g
                )
                .unwrap()
                .value()
                .unwrap());

            let setup_constraints = constraints_from_leaf
                + constraints_from_digest
                + constraints_from_params
                + constraints_from_path;

            println!(
                "number of constraints for verification: {}",
                cs.num_constraints() - setup_constraints
            );

            assert!(
                cs.is_satisfied().unwrap(),
                "verification constraints not satisfied"
            );
        }

    }

    #[test]
    fn good_root_test() {
        let mut rng = test_rng();
        let mut rand_leaves = || (0..2).map(|_| F::rand(&mut rng)).collect();

        let mut leaves: Vec<Vec<_>> = Vec::new();
        for _ in 0..128u8 {
            leaves.push(rand_leaves())
        }

        mmr_test(&leaves, false, Some((3, rand_leaves())))
    }

    #[test]
    #[should_panic]
    fn bad_root_test() {
        let mut rng = test_rng();
        let mut rand_leaves = || (0..2).map(|_| F::rand(&mut rng)).collect();

        let mut leaves: Vec<Vec<_>> = Vec::new();
        for _ in 0..128u8 {
            leaves.push(rand_leaves())
        }

        mmr_test(&leaves, true, Some((3, rand_leaves())))
    }
}
