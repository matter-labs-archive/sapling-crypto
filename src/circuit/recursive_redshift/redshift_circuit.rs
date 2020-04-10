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
use bellman::redshift::domains::*;

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
    // point raise to n-th power (n = vanishing size)
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
where E: Engine, O: OracleGadget<E, Commitment = AllocatedNum<E>>, T: ChannelGadget<E>, I: Iterator<Item = Option<E::Fr>>
{
    _engine_marker : std::marker::PhantomData<E>,
    _oracle_marker : std::marker::PhantomData<O>,
    _channel_marker : std::marker::PhantomData<T>,

    channel_params: T::Params,
    oracle_params: O::Params,
    fri_params: FriParams,
    input_stream: I,
    public_inputs : Vec<E::Fr>,
}


impl<E, O, T, I> RedShiftVerifierCircuit<E, O, T, I> 
where E: Engine, O: OracleGadget<E, Commitment = AllocatedNum<E>>, T: ChannelGadget<E>, I: Iterator<Item = Option<E::Fr>>, 
{
    pub fn new(channel_params: T::Params, oracle_params: O::Params, fri_params: FriParams, stream : I, public: Vec<E::Fr>) -> Self {

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

    pub fn get_fri_challenges<CS: ConstraintSystem<E>>(
        &self,
        cs : &mut CS,
        proof: &BatchedFriProof<E, O>,
        channel: &mut T,
    ) -> Result<Vec<AllocatedNum<E>>, SynthesisError> {
        
        let mut fri_challenges = vec![];
        fri_challenges.push(channel.produce_challenge(unnamed(cs))?);

        for commitment in proof.commitments.iter().cloned() {
            let iop_challenge = {
                channel.consume(commitment, cs)?;
                channel.produce_challenge(cs)?
            };

            fri_challenges.push(iop_challenge);
        }
        Ok(fri_challenges)
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
        let z_in_pow_n = AllocatedNum::pow(unnamed(cs), &z, decomposed_n.iter())?;

        let mut rhs : Num<E> = t_low_at_z.clone().into();
        let mid_term = t_mid_at_z.mul(unnamed(cs), &z_in_pow_n)?;
        rhs.mut_add_number_with_coeff(&mid_term, E::Fr::one());

        let z_in_pow_2n = z_in_pow_n.square(unnamed(cs))?;
        let highest_term = t_high_at_z.mul(unnamed(cs), &z_in_pow_2n)?;
        rhs.mut_add_number_with_coeff(&highest_term, E::Fr::one());

        // begin computing the lhs term

        // prepare public inputs 
        // TODO: check if I have taken the right domain (or increase by LDE factor?)

        let domain_size = n;
        let domain = Domain::<E::Fr>::new_for_size(domain_size as u64).expect("domain of this size should exist");
        let omega = domain.generator;
        let omega_inv = omega.inverse().expect("must exist");

        let l_0_at_z = evaluate_lagrange_poly(unnamed(cs), n, 0, &omega_inv, z.clone(), z_in_pow_n.clone())?;
        let mut PI_at_z = Num::zero();

        for (i, val) in self.public_inputs.into_iter().enumerate() {
            let input = AllocatedNum::alloc_input(cs.namespace(|| "allocating public input"), || Ok(val))?;
            let langrange_coef = match i {
                0 => l_0_at_z.clone(),
                _ => evaluate_lagrange_poly(unnamed(cs), n, i, &omega_inv, z.clone(), z_in_pow_n.clone())?,
            };
            let temp = input.mul(unnamed(cs),&langrange_coef)?;
            PI_at_z.sub_assign(&temp.into());
        }

        let mut inverse_vanishing_at_z = evaluate_inverse_vanishing_poly(unnamed(cs), n, &omega_inv, z.clone(), z_in_pow_n.clone())?;
        let l_n_minus_one_at_z = evaluate_lagrange_poly(unnamed(cs), n, n-1, &omega_inv, z.clone(), z_in_pow_n.clone())?;

        // (q_l a + q_r b + q_o c + q_m a * b + q_c + q_add_sel q_next) * inv_vanishing_poly

        let term1 = {
            let mut res : Num<E> = q_c_at_z.clone().into();

            res += q_l_at_z.mul(unnamed(cs), a_at_z)?;
            res += q_r_at_z.mul(unnamed(cs), b_at_z)?;  
            res += q_o_at_z.mul(unnamed(cs), c_at_z)?;
            res += q_m_at_z.mul(unnamed(cs), a_at_z)?;
        
            // add additional shifted selector
            res += q_add_sel_at_z.mul(unnamed(cs), &c_shifted_at_z)?;

            // add public inputs
            res += &PI_at_z;

            let res = Num::mul(unnamed(cs), &res, &inverse_vanishing_at_z.clone().into())?;
            res
        };

        // from now on: permutation check

        let n_fe = E::Fr::from_str(&n.to_string()).expect("must be valid field element");
        let mut two_n_fe = n_fe;
        two_n_fe.double();

        // TODO: think how to organize types to make it more readable
        // macros (usual one) would work
        // and do something to avoid clonings

        let term2 = {
            
            let mut res : Num<E> = z_1_at_z.clone().into();

            let mut tmp : Num<E> = s_id_at_z.mul(unnamed(cs), &beta)?.into();
            tmp += a_at_z.clone();
            tmp += gamma.clone();
            
            res = Num::mul(unnamed(cs), &res, &tmp)?.into();
            
            tmp = s_id_at_z.clone().into();
            tmp.add_assign(&Num::from_constant(&n_fe, cs));
            tmp = Num::mul(unnamed(cs), &tmp, &beta.clone().into())?.into();
            tmp += b_at_z.clone();
            tmp += gamma.clone();
            res = Num::mul(unnamed(cs), &res, &tmp)?.into();

            tmp = s_id_at_z.clone().into();
            tmp.add_assign(&Num::from_constant(&two_n_fe, cs));
            tmp = Num::mul(unnamed(cs), &tmp, &beta.clone().into())?.into();
            tmp += c_at_z.clone();
            tmp += gamma.clone();
            res = Num::mul(unnamed(cs), &res, &tmp)?.into();

            res -= z_1_shifted_at_z.clone();

            inverse_vanishing_at_z = inverse_vanishing_at_z.mul(unnamed(cs), &alpha)?;
            Num::mul(unnamed(cs), &res, &inverse_vanishing_at_z.clone().into())?
        };

        let term3 = {
            let mut res : Num<E> = z_2_at_z.clone().into();

            let mut tmp : Num<E> = sigma_1_at_z.mul(unnamed(cs), &beta)?.into();
            tmp += a_at_z.clone();
            tmp += gamma.clone();
            res = Num::mul(unnamed(cs), &res, &tmp)?.into();

            tmp = sigma_2_at_z.mul(unnamed(cs), &beta)?.into();
            tmp += b_at_z.clone();
            tmp += gamma.clone();
            res = Num::mul(unnamed(cs), &res, &tmp)?.into();

            tmp = sigma_3_at_z.mul(unnamed(cs), &beta)?.into();
            tmp += c_at_z.clone();
            tmp += gamma.clone();
            res = Num::mul(unnamed(cs), &res, &tmp)?.into();
           
            res -= z_1_shifted_at_z.clone();

            inverse_vanishing_at_z = inverse_vanishing_at_z.mul(unnamed(cs), &alpha)?;
            Num::mul(unnamed(cs), &res, &inverse_vanishing_at_z.clone().into())?
        };

        let term4 = {
            let mut res : Num<E> = z_1_shifted_at_z.clone().into();
            res -= z_2_shifted_at_z.clone();
            res = Num::mul(unnamed(cs), &res, &l_n_minus_one_at_z.clone().into())?.into();
            
            inverse_vanishing_at_z = inverse_vanishing_at_z.mul(unnamed(cs), &alpha)?;
            Num::mul(unnamed(cs), &res, &inverse_vanishing_at_z.clone().into())?
        };

        let term5 = {
            let mut res : Num<E> = z_1_at_z.clone().into();
            res -= z_2_at_z.clone();
            res = Num::mul(unnamed(cs), &res, &l_0_at_z.clone().into())?.into();

            inverse_vanishing_at_z = inverse_vanishing_at_z.mul(unnamed(cs), &alpha)?;
            Num::mul(unnamed(cs), &res, &inverse_vanishing_at_z.clone().into())?
        };

        let mut lhs = Num::zero();
        lhs += term1;
        lhs += term2;
        lhs += term3;
        lhs += term4;
        lhs += term5;

        // compare!
        let unit = Num::from_constant(&E::Fr::one(), cs);
        Num::enforce(
            cs.namespace(|| "Plonk equality check at point z"), 
            &lhs,
            &unit,
            &rhs,
        );

        // Fri validation starts from here

        let aggregation_challenge = channel.produce_challenge(unnamed(cs))?;

        let mut upper_layer_commitments = proof.commitments;
        upper_layer_commitments.extend(precomputation.data.iter().map(|item| {
            Labeled::new(item.label, item.data.commitment)
        }));
      
        let fri_challenges = self.get_fri_challenges(cs, &proof.fri_proof, &mut channel)?;
       
        let natural_first_element_indexes = (0..self.fri_params.R).map(|_| {
            let packed = channel.produce_challenge(unnamed(cs))?;
            let bits = packed.into_bits_le(unnamed(cs))?;
            bits.truncate(32);
            
            Ok(bits)
        }).collect::<Result<_,_>>()?;

        let fri_verifier_gadget = FriVerifierGadget::<E, O> {
            collapsing_factor : self.fri_params.collapsing_factor,
            //number of iterations done during FRI query phase
            num_query_rounds : self.fri_params.R,
            initial_degree_plus_one : self.fri_params.initial_degree_plus_one.get(),
            lde_factor: self.fri_params.lde_factor,
            //the degree of the resulting polynomial at the bottom level of FRI
            final_degree_plus_one : self.fri_params.final_degree_plus_one,

            _engine_marker : std::marker::PhantomData::<E>,
            _oracle_marker : std::marker::PhantomData::<O>,
        };

        let upper_layer_combiner : Option<u32> = None;
        
        let is_fri_valid = fri_verifier_gadget.verify_proof(
            cs.namespace(|| "verify FRI proof"),
            &self.oracle_params,
            upper_layer_combiner,
            &upper_layer_commitments,
            &proof.fri_proof.commitments,
            &proof.fri_proof.final_coefficients,
            &fri_challenges,
            natural_first_element_indexes,
            proof.fri_proof.fri_round_queries,
        )?;

        Boolean::enforce_equal(cs.namespace(|| "check output bit"), &is_fri_valid, &Boolean::constant(true));

        Ok(())
    }
}






