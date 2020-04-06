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


pub trait FromStream<E: Engine> {

    fn from_stream<CS, I>(cs: CS, iter: &I) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>, I: Iterator<Item = Option<E::Fr>>;
}

impl<E: Engine> FromStream<E> for AllocatedNum<E> {

}



type Commitment = AllocatedNum<E>;
    type Proof = Vec<AllocatedNum<E>>;

// pub trait from iterator


#[derive(Debug)]
pub struct SinglePolySetupData<F: PrimeField> {
    pub setup_value : Option<F>,
    pub commitment : Option<F>,
}


#[derive(Debug)]
pub struct RedshiftSetupPrecomputation<F: PrimeField> {
    // containes precomputations for:  
    // q_l, q_r, q_o, q_m, q_c, q_add_sel, s_id, sigma_1, sigma_2, sigma_3
    pub data : LabeledVec<SinglePolySetupData<F>>,
}


pub struct FriSingleQueryRoundData<E: Engine, I: OracleGadget<E>> {   
    upper_layer_queries: LabeledVec<Query<E, I>>,
    // this structure is modified internally as we simplify Nums during he work of the algorithm
    queries: Vec<Query<E, I>>,
    natural_first_element_index: Vec<Boolean>,
}



pub struct BatchedFriProof<F: PrimeField, I: OracleGadget<E>> {
    // commitments to all intermidiate oracles
    pub commitments: Vec<>,
    pub final_coefficients: Vec<F>,

    pub fri_round_query
    pub upper_layer_queries: Vec<Vec<(Label, I::Query)>>,
    pub queries: Vec<Vec<I::Query>>,
    //excluding the initial one oracle - it is simly the commitment, no need to repeat
    
}

pub struct RedshiftProof<F: PrimeField> {
    pub op
    pub a_opening_value: Option<F>,
    pub b_opening_value: Option<F>,
    pub c_opening_value: Option<F>,
    pub c_shifted_opening_value: Option<F>,
    pub q_l_opening_value: Option<F>,
    pub q_r_opening_value: Option<F>,
    pub q_o_opening_value: Option<F>,
    pub q_m_opening_value: Option<F>,
    pub q_c_opening_value: Option<F>,
    pub q_add_sel_opening_value: Option<F>,
    pub s_id_opening_value: Option<F>,
    pub sigma_1_opening_value: Option<F>,
    pub sigma_2_opening_value: Option<F>,
    pub sigma_3_opening_value: Option<F>,
    pub z_1_opening_value: Option<F>,
    pub z_2_opening_value: Option<F>,
    pub z_1_shifted_opening_value: Option<F>,
    pub z_2_shifted_opening_value: Option<F>,
    pub t_low_opening_value: Option<F>,
    pub t_mid_opening_value: Option<F>,
    pub t_high_opening_value: Option<F>,
    
    pub commitments: Vec<(Label, I::Commitment)>, 



    // pub batched_FRI_proof: FriProof<F, I>,
}