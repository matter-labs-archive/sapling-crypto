#[cfg(test)]
mod test {
    use bellman::redshift::redshift::tests::*;
    use bellman::redshift::redshift::serialization::*;
    
    use crate::circuit::recursive_redshift::redshift_circuit::*;
    use bellman::redshift::IOP::oracle::coset_combining_rescue_tree::*;
    use bellman::redshift::IOP::channel::rescue_channel::*;
    use bellman::redshift::IOP::hashes::rescue::bn256_rescue_params::BN256Rescue;
    use bellman::redshift::IOP::hashes::rescue::RescueParams;
    use bellman::pairing::bn256::Fr as Fr;
    
    #[test]
    fn redshift_recursion_for_fibbonacchi() 
    {
        type E = pairing::bn256::Bn256;
        type O<'a> = FriSpecificRescueTree<'a, Fr, BN256Rescue>;
        type T<'a> = RescueChannel<'a, Fr, BN256Rescue>;

        // prepare parameters
        let a = Fr::one();
        let b = Fr::one();
        let num_steps = 10;

        let fri_params = FriParams {
            initial_degree_plus_one: std::cell::Cell::new(0),
            lde_factor: 16,
            R: 4,
            collapsing_factor: 2,
            final_degree_plus_one: 1
        };

        let bn256_rescue_params = BN256Rescue::default();

        let oracle_params = RescueTreeParams {
            values_per_leaf: 1 << fri_params.collapsing_factor,
            rescue_params: &bn256_rescue_params,
            _marker: std::marker::PhantomData::<Fr>,
        };

        let channel_params = RescueChannelParams {
            rescue_params: &bn256_rescue_params,
            _marker: std::marker::PhantomData::<Fr>,
        };

        let res = redshift_template::<E, O, T>(
            a,
            b,
            num_steps,
            fri_params,
            oracle_params,
            channel_params,
        ).expect("should pass");

        let is_valid = res.0;
        let setup_precomp = res.1;
        let proof = res.2;

        assert_eq!(is_valid, true);

        let mut constainer = Vec::<Fr>::new();

        let coset_size = 1 << fri_params.collapsing_factor;
        let top_level_oracle_size = (fri_params.initial_degree_plus_one.get() * fri_params.lde_factor) / coset_size;
        let top_leve_height = log2_floor(top_level_oracle_size);

        setup_precomp.to_stream(&mut container, top_leve_height);
        proof.to_stream(&mut container, fri_params);

        let rescue_params = BN256Rescue::default();
        let oracle_params =  RescueTreeGadgetParams {
            num_elems_per_leaf: coset_size,
            rescue_params: &rescue_params,
            _marker: std::marker::PhantomData::<Fr>,
        };

        let redshift_recursion_circuit = RedShiftVerifierCircuit::new(
            &rescue_params,
            oracle_params, 
            fri_params, 
            container.into_iter(), 
            [a, b],
        );

        // verify that circuit is satifiable
        let mut test_assembly = TestAssembly::new();
        redshift_recursion_circuit.synthesize(&mut test_assembly)?;
        assert!(test_assembly.is_satisfied(false), "some constraints are not satisfied");

        println!("Num of constraints: {}", test_assembly.num_of_constraints());
    }
}
      

    