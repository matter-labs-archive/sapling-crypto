use bellman::pairing::{
    Engine,
};

use bellman::pairing::ff::{
    Field,
    PrimeField,
};

use bellman::{
    Circuit,
    SynthesisError,
    ConstraintSystem,
    LinearCombination,
    Variable,
    Namespace,
};
use bellman::redshift::IOP::FRI::coset_combining_fri::FriParams;

use crate::circuit::num::*;
use crate::circuit::boolean::*;

use crate::circuit::recursive_redshift::oracles::*;
use crate::circuit::recursive_redshift::channel::*;
use crate::circuit::recursive_redshift::fri_verifier::*;

use super::data_structs::*;

// TODO: FriParams are copyable - stop clonning!

pub fn find_by_label<'a, X>(label: Label, arr: &'a Vec<Labeled<X>>) -> Result<&'a X, SynthesisError> {

    arr.iter().find(|elem| elem.label == label).map(|elem| &elem.data).ok_or(SynthesisError::Unknown)
}


pub fn unnamed<'a, E: Engine, CS: ConstraintSystem<E>>(cs: &'a mut CS) -> Namespace<'a, E, CS::Root> {
    cs.namespace(|| "")
}


pub fn evaluate_inverse_vanishing_poly<E, CS>(
    mut cs: CS, 
    vahisning_size: usize,
    omega_inv : &E::Fr, 
    point: AllocatedNum<E>,
    point_in_pow_n : AllocatedNum<E>,
) -> Result<AllocatedNum<E>, SynthesisError> 
where E: Engine, CS: ConstraintSystem<E>
{
    assert!(vahisning_size.is_power_of_two());

    // update from the paper - it should not hold for the last generator, omega^(n) in original notations

    // Z(X) = (X^n - 1) / (X - omega^(n-1)) => Z^{-1}(X) = (X - omega^(n-1)) / (X^(n) - 1)
    // note that omega^(n-1) = omega^(-1)

    let mut numerator : Num<E> = point.into();
    numerator.sub_assign(&Num::from_constant(omega_inv, &cs));

    let mut denoninator : Num<E> = point_in_pow_n.into();
    denoninator.sub_assign(&Num::from_constant(&E::Fr::one(), &cs));

    Num::div(cs.namespace(|| "div"), &numerator, &denoninator)
}


pub fn evaluate_lagrange_poly<E: Engine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    vahisning_size: usize, 
    poly_number: usize,
    omega_inv : &E::Fr,
    point: AllocatedNum<E>,
    // point raise to m-th power
    point_pow : AllocatedNum<E>,
    point_in_pow_n : AllocatedNum<E>,
) -> Result<AllocatedNum<E>, SynthesisError> 
{
    assert!(vahisning_size.is_power_of_two());

    // L_0(X) = (Z_H(X) / (X - 1)) * (1/n) and L_0(1) = 1
    // L_k(omega) = 1 = L_0(omega * omega^-k)
    // L_k(z) = L_0(z * omega^-k) = (1/n) * (z^n - 1)/(z * omega^{-k} - 1)

    // TODO: I think the code above has a bug - the scale coefficient should be 1/(n-1) instead of n

    let mut numerator : Num<E> = point_in_pow_n.into();
    numerator.sub_assign(&Num::from_constant(&E::Fr::one, &cs));

    let omega_inv_pow = omega_inv.pow([poly_number as u64]);

    let mut denoninator : Num<E> = point.pow();
    denoninator.scale(omega_inv_pow);
    numerator.sub_assign(&Num::from_constant(&E::Fr::one, &cs));

    let mut repr = E::Fr::zero().into_repr();
    repr.as_mut()[0] = vahisning_size as u64;
    let size_fe = E::Fr::from_repr(repr).expect("is a valid representation");
    numerator.scale(size_fe);

    Num::div(cs.namespace(|| "div"), &numerator, &denoninator)
}




struct RedShiftVerifierCircuit<E, O, T, I> 
where E: Engine, O: OracleGadget<E>, T: ChannelGadget<E>, I: Iterator<Item = Option<E::Fr>>
{
    _engine_marker : std::marker::PhantomData<E>,
    _oracle_marker : std::marker::PhantomData<O>,
    _channel_marker : std::marker::PhantomData<T>,

    channel_params: T::Params,
    oracle_params: O::Params,
    fri_params: FriParams,
    input_stream: I,
    public_inputs : Vec<Option<E::Fr>>,
}


impl<E, O, T, I> RedShiftVerifierCircuit<E, O, T, I> 
where E: Engine, O: OracleGadget<E>, T: ChannelGadget<E>, I: Iterator<Item = Option<E::Fr>> 
{
    pub fn new(channel_params: T::Params, oracle_params: O::Params, fri_params: FriParams, stream : I, public: Vec<Option<E::Fr>>) -> Self {

        RedShiftVerifierCircuit {
            
            _engine_marker : std::marker::PhantomData::<E>,
            _oracle_marker : std::marker::PhantomData::<O>,
            _channel_marker : std::marker::PhantomData::<T>,

            channel_params,
            oracle_params,
            fri_params,
            input_stream: stream,
            public_inputs : public,
        }
    }
}


impl<E, O, T, I> Circuit<E> for RedShiftVerifierCircuit<E, O, T, I> 
where 
    E: Engine, O: OracleGadget<E, Commitment = AllocatedNum<E>>, T: ChannelGadget<E>, I: Iterator<Item = Option<E::Fr>>,
 {

     fn synthesize<CS: ConstraintSystem<E>>(
        mut self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {

        let coset_size = 1 << self.fri_params.collapsing_factor;
        let n = self.fri_params.initial_degree_plus_one.get();
        let top_level_oracle_size = (n * self.fri_params.lde_factor) / coset_size;
        let top_level_height = log2_floor(top_level_oracle_size);

        let mut channel = T::new(self.channel_params);
        
        let precomputation = RedshiftSetupPrecomputation::<E,O>::from_stream(
            cs.namespace(|| "initialize precomputation"), 
            &mut self.input_stream, 
            top_level_height,
        )?;

        let proof = RedshiftProof::<E, O>::from_stream(
            cs.namespace(|| "initialize proof"),
            &mut self.input_stream, 
            self.fri_params.clone(),
        )?;

        let a_com : &AllocatedNum<E> = find_by_label("a", &proof.commitments)?;
        channel.consume(a_com.clone(), unnamed(cs))?;
   
        let b_com : &AllocatedNum<E> = find_by_label("b", &proof.commitments)?;
        channel.consume(b_com.clone(), unnamed(cs))?;
        
        let c_com : &AllocatedNum<E> = find_by_label("c", &proof.commitments)?;
        channel.consume(c_com.clone(), unnamed(cs))?;

        let beta = channel.produce_challenge(unnamed(cs))?;
        let gamma = channel.produce_challenge(unnamed(cs))?;

        let z_1_com : &AllocatedNum<E> = find_by_label("z_1", &proof.commitments)?;
        channel.consume(z_1_com.clone(), unnamed(cs))?;
        
        let z_2_com : &AllocatedNum<E> = find_by_label("z_2", &proof.commitments)?; 
        channel.consume(z_2_com.clone(), unnamed(cs))?;

        let alpha = channel.produce_challenge(unnamed(cs))?;

        let t_low_com : &AllocatedNum<E> = find_by_label("t_low", &proof.commitments)?;
        channel.consume(t_low_com.clone(), unnamed(cs))?;
    
        let t_mid_com : &AllocatedNum<E> = find_by_label("t_mid", &proof.commitments)?;
        channel.consume(t_mid_com.clone(), unnamed(cs))?;

        let t_high_com : &AllocatedNum<E> = find_by_label("t_high", &proof.commitments)?;
        channel.consume(t_high_com.clone(), unnamed(cs))?;

        // TODO: we should be very carefule in choosing z!
        // at least it should be nonzero, but I suppose that it also should not been contained in our domain
        // add additiona constraints in order to ensure this!

        let z = channel.produce_challenge(unnamed(cs))?;

        // check the final equation at single point z!

        let a_at_z = find_by_label("a", &proof.opening_values)?;
        let b_at_z = find_by_label("b", &proof.opening_values)?;
        let c_at_z = find_by_label("c", &proof.opening_values)?;
        let c_shifted_at_z = find_by_label("c_shifted", &proof.opening_values)?;

        let q_l_at_z = find_by_label("q_l", &proof.opening_values)?;
        let q_r_at_z = find_by_label("q_r", &proof.opening_values)?;
        let q_o_at_z = find_by_label("q_o", &proof.opening_values)?;
        let q_m_at_z = find_by_label("q_m", &proof.opening_values)?;
        let q_c_at_z = find_by_label("q_c", &proof.opening_values)?;
        let q_add_sel_at_z = find_by_label("q_add_sel", &proof.opening_values)?;

        let s_id_at_z = find_by_label("s_id", &proof.opening_values)?;
        let sigma_1_at_z = find_by_label("sigma_1", &proof.opening_values)?;
        let sigma_2_at_z = find_by_label("sigma_2", &proof.opening_values)?;
        let sigma_3_at_z = find_by_label("sigma_3", &proof.opening_values)?;

        let z_1_at_z = find_by_label("z_1",  &proof.opening_values)?;
        let z_2_at_z = find_by_label("z_2", &proof.opening_values)?;

        let z_1_shifted_at_z = find_by_label("z_1_shifted", &proof.opening_values)?;
        let z_2_shifted_at_z = find_by_label("z_2_shifted", &proof.opening_values)?;

        let t_low_at_z = find_by_label("t_low", &proof.opening_values)?;
        let t_mid_at_z = find_by_label("t_mid", &proof.opening_values)?;
        let t_high_at_z = find_by_label("t_high", &proof.opening_values)?;

        // compute the righthandsize term: T_low(z) + T_mid(z) * z^n + T_high(z) * z^(2n)
        let decomposed_n = u64_into_boolean_vec_le(unnamed(cs), Some(n as u64))?;
        let z_in_pow_n = AllocatedNum::pow(unnamed(cs), &z, decomposed_n.iter())?;

        let mut rhs : Num<E> = t_low_at_z.clone().into();
        let mid_term = t_mid_at_z.mul(unnamed(cs), &z_in_pow_n)?;
        rhs.mut_add_number_with_coeff(&mid_term, E::Fr::one());

        let z_in_pow_2n = z_in_pow_n.square(unnamed(cs))?;
        let highest_term = t_high_at_z.mul(unnamed(cs), &z_in_pow_2n)?;
        rhs.mut_add_number_with_coeff(&highest_term, E::Fr::one());

        // begin computing the lhs term

//         let mut t_1 = {
//         let mut res = q_c_at_z;

//         let mut tmp = q_l_at_z;
//         tmp.mul_assign(&a_at_z);
//         res.add_assign(&tmp);

//         let mut tmp = q_r_at_z;
//         tmp.mul_assign(&b_at_z);
//         res.add_assign(&tmp);

//         let mut tmp = q_o_at_z;
//         tmp.mul_assign(&c_at_z);
//         res.add_assign(&tmp);

//         let mut tmp = q_m_at_z;
//         tmp.mul_assign(&a_at_z);
//         tmp.mul_assign(&b_at_z);
//         res.add_assign(&tmp);

//         // add additional shifted selector
//         let mut tmp = q_add_sel_at_z;
//         tmp.mul_assign(&c_shifted_at_z);
//         res.add_assign(&tmp);

//         // add public inputs
//         res.add_assign(&PI_at_z);

//         // no need for the first one
//         //inverse_vanishing_at_z.mul_assign(&alpha);

//         res.mul_assign(&inverse_vanishing_at_z);

//         res
//     };

        

        Ok(())
    }
}
            







//     let mut t_1 = {
//         let mut res = q_c_at_z;

//         let mut tmp = q_l_at_z;
//         tmp.mul_assign(&a_at_z);
//         res.add_assign(&tmp);

//         let mut tmp = q_r_at_z;
//         tmp.mul_assign(&b_at_z);
//         res.add_assign(&tmp);

//         let mut tmp = q_o_at_z;
//         tmp.mul_assign(&c_at_z);
//         res.add_assign(&tmp);

//         let mut tmp = q_m_at_z;
//         tmp.mul_assign(&a_at_z);
//         tmp.mul_assign(&b_at_z);
//         res.add_assign(&tmp);

//         // add additional shifted selector
//         let mut tmp = q_add_sel_at_z;
//         tmp.mul_assign(&c_shifted_at_z);
//         res.add_assign(&tmp);

//         // add public inputs
//         res.add_assign(&PI_at_z);

//         // no need for the first one
//         //inverse_vanishing_at_z.mul_assign(&alpha);

//         res.mul_assign(&inverse_vanishing_at_z);

//         res
//     };

//     let n_fe = E::Fr::from_str(&n.to_string()).expect("must be valid field element");
//     let mut two_n_fe = n_fe;
//     two_n_fe.double();

//     {
//         let mut res = z_1_at_z;

//         let mut tmp = s_id_at_z;
//         tmp.mul_assign(&beta);
//         tmp.add_assign(&a_at_z);
//         tmp.add_assign(&gamma);
//         res.mul_assign(&tmp);

//         let mut tmp = s_id_at_z;
//         tmp.add_assign(&n_fe);
//         tmp.mul_assign(&beta);
//         tmp.add_assign(&b_at_z);
//         tmp.add_assign(&gamma);
//         res.mul_assign(&tmp);

//         let mut tmp = s_id_at_z;
//         tmp.add_assign(&two_n_fe);
//         tmp.mul_assign(&beta);
//         tmp.add_assign(&c_at_z);
//         tmp.add_assign(&gamma);
//         res.mul_assign(&tmp);

//         res.sub_assign(&z_1_shifted_at_z);

//         inverse_vanishing_at_z.mul_assign(&alpha);

//         res.mul_assign(&inverse_vanishing_at_z);

//         t_1.add_assign(&res);
//     }

//     {
//         let mut res = z_2_at_z;

//         let mut tmp = sigma_1_at_z;
//         tmp.mul_assign(&beta);
//         tmp.add_assign(&a_at_z);
//         tmp.add_assign(&gamma);
//         res.mul_assign(&tmp);

//         let mut tmp = sigma_2_at_z;
//         tmp.mul_assign(&beta);
//         tmp.add_assign(&b_at_z);
//         tmp.add_assign(&gamma);
//         res.mul_assign(&tmp);

//         let mut tmp = sigma_3_at_z;
//         tmp.mul_assign(&beta);
//         tmp.add_assign(&c_at_z);
//         tmp.add_assign(&gamma);
//         res.mul_assign(&tmp);

//         res.sub_assign(&z_2_shifted_at_z);

//         inverse_vanishing_at_z.mul_assign(&alpha);

//         res.mul_assign(&inverse_vanishing_at_z);

//         t_1.add_assign(&res);
//     }

//     {
//         let mut res = z_1_shifted_at_z;
//         res.sub_assign(&z_2_shifted_at_z);
//         res.mul_assign(&l_n_minus_one_at_z);

//         inverse_vanishing_at_z.mul_assign(&alpha);

//         res.mul_assign(&inverse_vanishing_at_z);

//         t_1.add_assign(&res);
//     }

//     {
//         let mut res = z_1_at_z;
//         res.sub_assign(&z_2_at_z);
//         res.mul_assign(&l_0_at_z);

//         inverse_vanishing_at_z.mul_assign(&alpha);

//         res.mul_assign(&inverse_vanishing_at_z);

//         t_1.add_assign(&res);
//     }

//     if t_1 != t_at_z {
//         println!("Recalculated t(z) is not equal to the provided value");
//         return Ok(false);
//     }

//     let aggregation_challenge = channel.produce_field_element_challenge();

//     let domain_size = n * fri_params.lde_factor;
//     let domain = Domain::<E::Fr>::new_for_size((domain_size) as u64)?;
//     let omega = domain.generator;

//     let upper_layer_combiner = |arr: Vec<(Label, &E::Fr)>| -> Option<E::Fr> {
//         fn find_poly_value_at_omega<T>(label: Label, arr: &Vec<(Label, T)>) -> Option<&T> {
//             arr.iter().find(|(l, _)| *l == label).map(|(_, c)| c)
//         }

//         // given an evaluation point x and auxiliarly point x_1,
//         // aggregation_challenge = alpha (the final value of alpha is also returned!)
//         // and an array of pairs (f_i(x), f_i(x_1)) - one pair for each polynomial f_i(t) in question (i \in [0, 1, .., n])
//         // this function computes: 
//         // y = /sum alpha^i [f_i(x) - f_i(x_1)]/ [x - x_1]
//         // and returns the pair (y, final_alpha)

//         fn combine_at_single_point<F: PrimeField>(pairs: Vec<(&F, F)>, x: &F, x_1: &F, alpha: &F) -> (F, F) {

//             let mut res = F::zero();
//             let mut aggr_mult = F::one();

//             for (&a, b) in pairs.iter() {
//                 // separately compute numerators
//                 let mut temp = a;
//                 temp.sub_assign(&b);
//                 temp.mul_assign(&aggr_mult);

//                 res.add_assign(&temp);
//                 aggr_mult.mul_assign(alpha);
//             }

//             // now compute the common denominator
//             let mut temp = *x;
//             temp.sub_assign(x_1);
//             temp = temp.inverse().expect("must exist");
//             res.mul_assign(&temp);

//             (res, aggr_mult)
//         }

//         // given an evaluation point x and two auxiliarly points x_1, x_2,
//         // aggregation_challenge = alpha (the final value of alpha is also returned!)
//         // and an array of triples (f_i(x), f_i(x_1), f_i(x_2)) - one triple for each polynomial f_i(t) in question (i \in [0, 1, .., n])
//         // this function computes: 
//         // y = /sum alpha^i [f_i(x) - U_i(x)]/ [(x - x_1)(x - x_2)]
//         // where U_i(t) is the unique linear function, having value f_i(x_1) at x_1 and f_i(x_2) at x_2
//         // note that such U_i(t) = f_i(x_1) + [t - x_1]/ [x_2 - x_1] (f_i(x_2) - f_i(x_1))  and hence
//         // U_i(x) = f_i(x_1) + [x - x_1]/ [x_2 - x_1] (f_i(x_2) - f_i(x_1))
//         // this means that all U_i(x) share the common slope [x - x_1] / [x_2 - x_1]
//         // which therefore may be precomputed once and forall
//         // funtion returns the pair (y, final_alpha)

//         fn combine_at_two_points<F: PrimeField>(triples: Vec<(&F, F, F)>, x: &F, x_1: &F, x_2: &F, alpha: &F) -> (F, F) {
            
//             // precompute the common slope
//             let mut slope = *x;
//             slope.sub_assign(x_1);
//             let mut slope_denum = *x_2;
//             slope_denum.sub_assign(x_1);
//             slope.mul_assign(&slope_denum.inverse().expect("must exist"));

//             let mut res = F::zero();
//             let mut aggr_mult = F::one();

//             for (&f_x, f_x_1, f_x_2) in triples.iter() {

//                 //evaluate interpolation poly -U_i(x) = -f_x_1 - slope * (f_x_2 - f_x_1) = slope * (f_x_1 - f_x_2) - f_x_1
//                 let mut temp = f_x_1.clone();
//                 temp.sub_assign(&f_x_2);
//                 temp.mul_assign(&slope);
//                 temp.sub_assign(&f_x_1);

//                 // compute nominator: aggr_mult * (f_x - U_i(x))
//                 temp.add_assign(&f_x);
//                 temp.mul_assign(&aggr_mult);

//                 res.add_assign(&temp);
//                 aggr_mult.mul_assign(alpha);
//             }

//             // now compute the common denominator
//             // (x - x_1)(x - x_2) = x^2 - (x_1 + x_2) * x + x_1 * x_2
//             let mut t_0 = *x_1;
//             t_0.add_assign(x_2);
//             let mut t_1 = *x_1;
//             t_1.mul_assign(&x_2);

//             let mut common_denominator = *x;
//             common_denominator.double();
//             common_denominator.sub_assign(&t_0);
//             common_denominator.add_assign(&t_1);
            
//             res.mul_assign(&common_denominator.inverse().expect("must exist"));
//             (res, aggr_mult)

//         }

//         let evaluation_point = find_poly_value_at_omega("evaluation_point", &arr)?;

//         // combine polynomials a, b, t_low, t_mid, t_high,
//         // which are opened only at z
//         let pairs : Vec<(&E::Fr, E::Fr)> = vec![
//             (find_poly_value_at_omega("a", &arr)?, a_at_z),
//             (find_poly_value_at_omega("b", &arr)?, b_at_z),
//             (find_poly_value_at_omega("t_low", &arr)?, t_low_at_z),
//             (find_poly_value_at_omega("t_mid", &arr)?, t_mid_at_z),
//             (find_poly_value_at_omega("t_high", &arr)?, t_high_at_z),
//         ];

//         let (mut res1, mut alpha1) = combine_at_single_point(pairs, &evaluation_point, &z, &aggregation_challenge);

//         // combine witness polynomials z_1, z_2, c which are opened at z and z * omega

//         let mut z_shifted = z;
//         z_shifted.mul_assign(&omega);

//         let witness_triples : Vec<(&E::Fr, E::Fr, E::Fr)> = vec![
//             (find_poly_value_at_omega("z_1", &arr)?, z_1_at_z, z_1_shifted_at_z),
//             (find_poly_value_at_omega("z_2", &arr)?, z_2_at_z, z_2_shifted_at_z),
//             (find_poly_value_at_omega("c", &arr)?, c_at_z, c_shifted_at_z),
//         ];

//         let (mut res2, alpha2) = combine_at_two_points(witness_triples, &evaluation_point, &z, &z_shifted, &aggregation_challenge);

//         // finally combine setup polynomials q_l, q_r, q_o, q_m, q_c, q_add_sel, s_id, sigma_1, sigma_2, sigma_3
//         // which are opened at z and z_setup
//         // in current implementation we assume that setup point is the same for all circuit-defining polynomials!

//         let setup_aux = vec![
//             &setup_precomp.q_l_aux, &setup_precomp.q_r_aux, &setup_precomp.q_o_aux, &setup_precomp.q_m_aux, 
//             &setup_precomp.q_c_aux, &setup_precomp.q_add_sel_aux, &setup_precomp.s_id_aux, &setup_precomp.sigma_1_aux, 
//             &setup_precomp.sigma_2_aux, &setup_precomp.sigma_3_aux,
//         ];
//         assert!(setup_aux.windows(2).all(|w| w[0].setup_point == w[1].setup_point));
//         let common_setup_point = setup_precomp.q_l_aux.setup_point;

//         let setup_triples : Vec<(&E::Fr, E::Fr, E::Fr)> = vec![
//             (find_poly_value_at_omega("q_l", &arr)?, q_l_at_z, setup_precomp.q_l_aux.setup_value),
//             (find_poly_value_at_omega("q_r", &arr)?, q_r_at_z, setup_precomp.q_r_aux.setup_value),
//             (find_poly_value_at_omega("q_o", &arr)?, q_o_at_z, setup_precomp.q_o_aux.setup_value),
//             (find_poly_value_at_omega("q_m", &arr)?, q_m_at_z, setup_precomp.q_m_aux.setup_value),
//             (find_poly_value_at_omega("q_c", &arr)?, q_c_at_z, setup_precomp.q_c_aux.setup_value),
//             (find_poly_value_at_omega("q_add_sel", &arr)?, q_add_sel_at_z, setup_precomp.q_add_sel_aux.setup_value),
//             (find_poly_value_at_omega("s_id", &arr)?, s_id_at_z, setup_precomp.s_id_aux.setup_value),
//             (find_poly_value_at_omega("sigma_1", &arr)?, sigma_1_at_z, setup_precomp.sigma_1_aux.setup_value),
//             (find_poly_value_at_omega("sigma_2", &arr)?, sigma_2_at_z, setup_precomp.sigma_2_aux.setup_value),
//             (find_poly_value_at_omega("sigma_3", &arr)?, sigma_3_at_z, setup_precomp.sigma_3_aux.setup_value),
//         ];

//         let (mut res3, _) = combine_at_two_points(setup_triples, &evaluation_point, &z, &common_setup_point, &aggregation_challenge);

//         // res = res1 + res2 * alpha_1 + res_3 * alpha_1 * alpha_2
//         res2.mul_assign(&alpha1);
//         res1.add_assign(&res2);
//         alpha1.mul_assign(&alpha2);
//         res3.mul_assign(&alpha1);
//         res1.add_assign(&res3);

//         Some(res1)
//     };

//     let setup_poly_commitmetns = vec![
//         ("q_l", setup_precomp.q_l_aux.oracle.get_commitment()),
//         ("q_r", setup_precomp.q_r_aux.oracle.get_commitment()),
//         ("q_o", setup_precomp.q_o_aux.oracle.get_commitment()),
//         ("q_m", setup_precomp.q_m_aux.oracle.get_commitment()),
//         ("q_c", setup_precomp.q_c_aux.oracle.get_commitment()),
//         ("q_add_sel", setup_precomp.q_add_sel_aux.oracle.get_commitment()),
//         ("s_id", setup_precomp.s_id_aux.oracle.get_commitment()),
//         ("sigma_1", setup_precomp.sigma_1_aux.oracle.get_commitment()),
//         ("sigma_2", setup_precomp.sigma_2_aux.oracle.get_commitment()),
//         ("sigma_3", setup_precomp.sigma_3_aux.oracle.get_commitment()),
//     ];

//     let mut upper_layer_commitments = proof.commitments.clone();
//     upper_layer_commitments.extend(setup_poly_commitmetns.into_iter());
      
//     let fri_challenges = FriIop::get_fri_challenges(
//         &proof.batched_FRI_proof,
//         &mut channel,
//         fri_params,
//     ); 
//     let natural_first_element_indexes = (0..fri_params.R).map(|_| channel.produce_uint_challenge() as usize % domain_size).collect();

//     let is_valid = FriIop::<E::Fr, I, T>::verify_proof_queries(
//         &proof.batched_FRI_proof,
//         upper_layer_commitments,
//         natural_first_element_indexes,
//         &fri_challenges[..],
//         &fri_params,
//         oracle_params,
//         upper_layer_combiner)?;

//     Ok(is_valid)
// }