use super::fri_utils::*;
use crate::circuit::recursive_redshift::oracles::*;

use bellman::pairing::{
    Engine,
};
use bellman::{
    SynthesisError,
    ConstraintSystem,
};

use bellman::pairing::ff::{
    Field,
    PrimeField,
};

use crate::circuit::num::*;
use crate::circuit::boolean::*;


pub struct FriVerifierGadget<E: Engine, I: OracleGadget<E>> {
    _engine_marker : std::marker::PhantomData<E>,
    _oracle_marker : std::marker::PhantomData<I>,
}

pub type Label = &'static str;
pub type CombinerFunction<E> = dyn Fn(&[(Labeled<&AllocatedNum<E>>)]) -> Result<AllocatedNum<E>, SynthesisError>;

pub struct Labeled<T> {
    pub label: Label,
    pub data: T,
}


impl<E: Engine, I: OracleGadget<E>> FriVerifierGadget<E, I> {

    pub fn verify_single_proof_round<CS: ConstraintSystem<E>>(
        
        mut cs: CS,

        upper_layer_queries: &[Labeled<Query<E, I>>],
        upper_layer_commitments: &[Labeled<I::Commitment>], 
        upper_layer_combiner: &CombinerFunction<E>,

        queries: &[Query<E, I>],
        commitments: &[I::Commitment],
        final_coefficients: &[AllocatedNum<E>],

        natural_first_element_index: &[Boolean],
        fri_challenges: &[AllocatedNum<E>],
        
        initial_domain_size: usize,
        collapsing_factor: usize,
        oracle_params: &I::Params,
   
    ) -> Result<Boolean, SynthesisError>
    {
        let mut fri_helper = FriUtilsGadget::<E>::new(initial_domain_size, collapsing_factor);
        let mut coset_idx = fri_helper.get_coset_idx_for_natural_index(natural_first_element_index);
        let coset_size = 1 << collapsing_factor;

        // check oracle proof for each element in the upper layer!
        let oracle = I::new(oracle_params);
        let mut final_result = Boolean::Constant(true);

        for labeled_query in upper_layer_queries.iter() {

            let label = &labeled_query.label;
            let commitment_idx = upper_layer_commitments.iter().position(|x| x.label == *label).ok_or(SynthesisError::Unknown)?;
            let commitment = &upper_layer_commitments[commitment_idx].data;
            let oracle_check = oracle.validate(
                cs.namespace(|| "Oracle proof"),
                fri_helper.get_log_domain_size(),
                &labeled_query.data.values, 
                coset_idx,
                commitment, 
                &labeled_query.data.proof, 
            )?;

            final_result = Boolean::and(cs.namespace(|| "and"), &final_result, &oracle_check)?;
        }
      
        // apply combiner function in order to conduct Fri round consistecy check
        // with respect to the topmost layer
        // let n be the size of coset
        // let the values contained inside queries to be (a_1, a_2, ..., a_n), (b_1, b_2, ..., b_n) , ..., (c_1, ..., c_n)
        // Coset combining function F constructs new vector of length n: (d_1, ..., d_n) via the following_rule : 
        // d_i = F(a_i, b_i, ..., c_i, x_i), i in (0..n)
        // here additiona argument x_i is the evaluation point and is defined by the following rule:
        // if the coset idx has bit representation xxxxxxxx, then x_i = w^(bitreverse(yyyy)|xxxxxxx)
        // here i = |yyyy| (bit decomposition)
        // From this we see that the only common constrained part for all x_i is coset_omega = w^(xxxxxx)
        // and to get corresponding x_i we need to multiply coset_omega by constant c_i = w^(bitreverse(yyyy)|000000)
        // if g = w^(100000) then c_i = w^(bitreverse(yyyy) * 1000000) = g^(bitreverse(yyyy))
        // constants c_i are easily deduced from domain parameters
        // construction of x_i is held by fri_utils

        let mut values = Vec::with_capacity(coset_size);
        let evaluation_points = fri_helper.get_combiner_eval_points(coset_idx)?;

        
    // for (i, coset_idx) in coset_idx_range.clone().enumerate() {
    //         let mut argument : Vec<(Label, &F)> = upper_layer_queries.iter().map(|x| (x.0, &x.1.values()[i])).collect();
    //         let natural_idx = CosetCombiner::get_natural_idx_for_coset_index(
    //             coset_idx, initial_domain_size, log_initial_domain_size, collapsing_factor);
    //         let evaluation_point = omega.pow([natural_idx as u64]);
    //         argument.push(("evaluation_point", &evaluation_point));
    //         let combined_value = upper_layer_combiner(argument).ok_or(SynthesisError::AssignmentMissing)?;
    //         values.push(combined_value);
    //     }
        

        // let mut domain_size = initial_domain_size;
        // let mut log_domain_size = log_initial_domain_size;
        // let mut elem_index = (natural_first_element_index << collapsing_factor) % domain_size;
        // let mut omega_inv = omega_inv.clone();
        // let mut previous_layer_element = FriIop::<F, O, C>::coset_interpolant_value(
        //     &values[..],
        //     &fri_challenges[0],
        //     coset_idx_range,
        //     collapsing_factor,
        //     coset_size,
        //     &mut domain_size,
        //     &mut log_domain_size,
        //     &mut elem_index,
        //     & mut omega_inv,
        //     two_inv);

        // for ((query, commitment), challenge) 
        //     in queries.into_iter().zip(commitments.iter()).zip(fri_challenges.iter().skip(1)) 
        // {
        //     //check query cardinality here!
        //     if query.card() != domain_size {
        //         return Ok(false);
        //     }

        //     //we do also need to check that coset_indexes are consistent with query
        //     let (coset_idx_range, elem_tree_idx) = CosetCombiner::get_coset_idx_for_natural_index_extended(
        //         elem_index, domain_size, log_domain_size, collapsing_factor);
            
        //     assert_eq!(coset_idx_range.len(), coset_size);

        //     if query.indexes() != coset_idx_range {
        //         return Ok(false);
        //     }              
        //     <O as Oracle<F>>::verify_query(commitment, query, &oracle_params);
            
        //     //round consistency check
        //     let this_layer_element = FriIop::<F, O, C>::coset_interpolant_value(
        //         query.values(),
        //         &challenge,
        //         coset_idx_range,
        //         collapsing_factor,
        //         coset_size,
        //         &mut domain_size,
        //         &mut log_domain_size,
        //         &mut elem_index,
        //         & mut omega_inv,
        //         two_inv);
         
        //     if previous_layer_element != query.values()[elem_tree_idx] {
        //         return Ok(false);
        //     }
        //     previous_layer_element = this_layer_element;
        // }

        // // finally we need to get expected value from coefficients
        // let mut expected_value_from_coefficients = F::zero();
        // let mut power = F::one();
        // let evaluation_point = omega.pow([elem_index as u64]);

        // for c in final_coefficients.iter() {
        //     let mut tmp = power;
        //     tmp.mul_assign(c);
        //     expected_value_from_coefficients.add_assign(&tmp);
        //     power.mul_assign(&evaluation_point);
        // }
        // Ok(expected_value_from_coefficients == previous_layer_element)

        Ok(result)
    }
}


    




// pub fn verify_proof_queries<Func: Fn(Vec<(Label, &F)>) -> Option<F>>(
//         proof: &FriProof<F, O>,
//         upper_layer_commitments: Vec<(Label, O::Commitment)>,
//         natural_element_indexes: Vec<usize>,
//         fri_challenges: &[F],
//         params: &FriParams,
//         oracle_params: &O::Params,
//         upper_layer_combiner: Func,
//     ) -> Result<bool, SynthesisError> {

//         assert!(fri_challenges.len() == proof.commitments.len());
//         assert!(proof.queries.len() == params.R);
//         assert!(natural_element_indexes.len() == proof.queries.len());

//         let mut two = F::one();
//         two.double();

//         let two_inv = two.inverse().ok_or(
//             SynthesisError::DivisionByZero
//         )?;

//         let domain = Domain::<F>::new_for_size((params.initial_degree_plus_one.get() * params.lde_factor) as u64)?;

//         let omega = domain.generator;
//         let omega_inv = omega.inverse().ok_or(
//             SynthesisError::DivisionByZero
//         )?;

//         let collapsing_factor = params.collapsing_factor;
//         let coset_size = 1 << collapsing_factor;
//         let initial_domain_size = domain.size as usize;
//         let log_initial_domain_size = log2_floor(initial_domain_size) as usize;

//         if natural_element_indexes.len() != params.R || proof.final_coefficients.len() > params.final_degree_plus_one {
//             return Ok(false);
//         }

//         let num_steps = 
//             log2_floor(params.initial_degree_plus_one.get() / params.final_degree_plus_one) / params.collapsing_factor as u32;
        
//         for ((round, natural_first_element_index), upper_layer_query) in 
//             proof.queries.iter().zip(natural_element_indexes.into_iter()).zip(proof.upper_layer_queries.iter()) {
            
//             let valid = FriIop::<F, O, C>::verify_single_proof_round::<Func>(
//                 &upper_layer_query,
//                 &upper_layer_commitments,
//                 &upper_layer_combiner,
//                 round,
//                 &proof.commitments,
//                 &proof.final_coefficients,
//                 natural_first_element_index,
//                 fri_challenges,
//                 num_steps as usize,
//                 initial_domain_size,
//                 log_initial_domain_size,
//                 collapsing_factor,
//                 coset_size,
//                 &oracle_params,
//                 &omega,
//                 &omega_inv,
//                 &two_inv,
//             )?;

//             if !valid {
//                 return Ok(false);
//             }
//         }

//         return Ok(true);
//     }