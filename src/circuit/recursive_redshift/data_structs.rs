use bellman::pairing::{
    Engine,
};
use bellman::pairing::ff::{
    Field,
    PrimeField,
};
use bellman::{
    SynthesisError,
    ConstraintSystem,
};
use crate::circuit::num::*;
use crate::circuit::boolean::*;

use crate::circuit::recursive_redshift::oracles::{OracleGadget, Query};


pub type Label = &'static str;
pub type CombinerFunction<E> = dyn Fn(Vec<Labeled<&Num<E>>>) -> Result<Num<E>, SynthesisError>;

#[derive(Debug)]
pub struct Labeled<T> {
    pub label: Label,
    pub data: T,
}

pub type LabeledVec<T> = Vec<Labeled<T>>;
pub type OracleHeight = usize;

pub trait FromStream<E: Engine, SPP> : Sized {

    fn from_stream<CS, I>(cs: CS, iter: &mut I, params : SPP) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>, I: Iterator<Item = Option<E::Fr>>;
}

impl<E: Engine, SPP> FromStream<E, SPP> for AllocatedNum<E> {
    fn from_stream<CS: ConstraintSystem<E>, I: Iterator<Item = Option<E::Fr>>>(
        mut cs: CS, 
        iter: &mut I,
        _params: SPP,
        ) -> Result<Self, SynthesisError> 
    {
        AllocatedNum::alloc2( cs.namespace(|| ""), iter.next().unwrap()) 
    } 
}

impl<E: Engine, T: FromStream<E, ()>> FromStream<E, usize> for Vec<T> {
    fn from_stream<CS: ConstraintSystem<E>, I: Iterator<Item = Option<E::Fr>>>(
        mut cs: CS,
        iter: &mut I,
        count: usize) -> Result<Self, SynthesisError> 
    {
        let arr : Result<Vec<_>, _> = (0..count).map(|_| { 
            let e = T::from_stream(cs.namespace(|| ""), &mut iter, () );
            e
        }).collect();
        arr
    }
}


pub struct SinglePolySetupData<E: Engine, I: OracleGadget<E>> {
    pub setup_value : AllocatedNum<E>,
    pub commitment : I::Commitment,
}


pub struct RedshiftSetupPrecomputation<E: Engine, I: OracleGadget<E>> {
    // containes precomputations for:  
    // q_l, q_r, q_o, q_m, q_c, q_add_sel, s_id, sigma_1, sigma_2, sigma_3
    pub data : LabeledVec<SinglePolySetupData<E, I>>,
    pub setup_point: AllocatedNum<E>,
}


pub struct FriSingleQueryRoundData<E: Engine, I: OracleGadget<E>> {   
    pub upper_layer_queries: LabeledVec<Query<E, I>>,
    // this structure is modified internally as we simplify Nums during he work of the algorithm
    pub queries: Vec<Query<E, I>>,
}


pub struct BatchedFriProof<E: Engine, I: OracleGadget<E>> {
    // commitments to all intermidiate oracles
    pub commitments: Vec<I::Commitment>,
    pub final_coefficients: Vec<AllocatedNum<E>>,
    pub fri_round_queries : Vec<FriSingleQueryRoundData<E, I>>,
}

pub struct RedshiftProof<E: Engine, I: OracleGadget<E>> {
    // containes opening values for:
    // a, b, c, c_shifted, q_l, q_r, q_o, q_m, q_c, q_add_sel, 
    // s_id, sigma_1, sigma_2, sigma_3,
    // z_1, z_2, z_1_shifted, z_2_shifted, t_low, t_mid, t_high
    pub opening_values: LabeledVec<AllocatedNum<E>>,
    // contains commitments for a, b, c, z_1, z_2, t_low, t_mid, t_high
    pub commitments: LabeledVec<I::Commitment>,
    pub fri_proof: BatchedFriProof<E, I>,
}


impl<E: Engine, I: OracleGadget<E>, OracleHeight> FromStream<E, OracleHeight> for SinglePolySetupData<E, I>
{
    fn from_stream<CS: ConstraintSystem<E>, I: Iterator<Item = Option<E::Fr>>>(
        mut cs: CS, 
        iter: &mut I,
        params: OracleHeight,
    ) -> Result<Self, SynthesisError> 
    {
        let setup_value = AllocatedNum::from_stream(cs.na)
        AllocatedNum::alloc2( cs.namespace(|| ""), iter.next().unwrap()) 
    } 
    
    SinglePolySetupData {
        pub setup_value : AllocatedNum<E>,
    pub commitment : I::Commitment,
    }
}


//RedshiftSetupPrecomputation<E: Engine, I: OracleGadget<E>>
// FriSingleQueryRoundData
//BatchedFriProof
//RedshiftProof