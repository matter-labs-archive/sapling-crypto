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
    numerator.sub_assign(&Num::from_constant(&E::Fr::one(), &cs));

    let omega_inv_pow = omega_inv.pow([poly_number as u64]);

    let mut denoninator : Num<E> = point.into();
    denoninator.scale(omega_inv_pow);
    numerator.sub_assign(&Num::from_constant(&E::Fr::one(), &cs));

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

        let mut z = channel.produce_challenge(unnamed(cs))?;

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
        let simplified_z = z.simplify(unnamed(cs))?;
        let z_in_pow_n = AllocatedNum::pow(unnamed(cs), &simplified_z, decomposed_n.iter())?;

        let mut rhs : Num<E> = t_low_at_z.clone().into();
        let mid_term = t_mid_at_z.mul(unnamed(cs), &z_in_pow_n)?;
        rhs.mut_add_number_with_coeff(&mid_term, E::Fr::one());

        let z_in_pow_2n = z_in_pow_n.square(unnamed(cs))?;
        let highest_term = t_high_at_z.mul(unnamed(cs), &z_in_pow_2n)?;
        rhs.mut_add_number_with_coeff(&highest_term, E::Fr::one());

        // begin computing the lhs term

        // prepare public inputs 

        // let l_0_at_z = evaluate_lagrange_poly::<E>(required_domain_size, 0, z);
   
        // let mut PI_at_z = E::Fr::zero();
        // for (i, val) in public_inputs.iter().enumerate() {
        //     if i == 0 {
        //         let mut temp = l_0_at_z;
        //         temp.mul_assign(val);
        //         PI_at_z.sub_assign(&temp);
        //     }
        //     else {
        //         // TODO: maybe make it multithreaded
        //         let mut temp = evaluate_lagrange_poly::<E>(required_domain_size, i, z);
        //         temp.mul_assign(val);
        //         PI_at_z.sub_assign(&temp);
        //     }
        // }

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
            






