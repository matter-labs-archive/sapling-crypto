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

use crate::circuit::recursive_redshift::oracles::{OracleGadget};

use bellman::redshift::IOP::FRI::coset_combining_fri::FriParams;


pub fn log2_floor(num: usize) -> usize {
    assert!(num > 0);
    let mut pow: usize = 0;

    while (1 << (pow+1)) <= num {
        pow += 1;
    }
    pow
}

// TODO: better replace by tag = ENUM
pub type Label = &'static str;
pub type CombinerFunction<E> = dyn Fn(Vec<Labeled<&AllocatedNum<E>>>, &Num<E>) -> Result<AllocatedNum<E>, SynthesisError>;


pub struct Labeled<T> {
    pub label: Label,
    pub data: T,
}

impl<T> Labeled<T> {
    pub fn new(label: Label, data: T) -> Self {
        Labeled {label, data}
    }
}

pub type LabeledVec<T> = Vec<Labeled<T>>;
pub type OracleHeight = usize;
pub type CosetSize = usize;

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

impl<E: Engine, T: FromStream<E, ()>> FromStream<E, (usize)> for Vec<T> {
    fn from_stream<CS: ConstraintSystem<E>, I: Iterator<Item = Option<E::Fr>>>(
        mut cs: CS,
        iter: &mut I,
        count: usize,
    ) -> Result<Self, SynthesisError> 
    {
        let arr : Result<Vec<_>, _> = (0..count).map(|_| { 
            let e = T::from_stream(cs.namespace(|| ""), iter, () );
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
    pub setup_point: AllocatedNum<E>,
    // containes precomputations for:  
    // q_l, q_r, q_o, q_m, q_c, q_add_sel, s_id, sigma_1, sigma_2, sigma_3
    pub data : LabeledVec<SinglePolySetupData<E, I>>,
}


// container that holds the values alongside the proof 
// NB: there is no need to store the index (or path), as it is calculated and checked by verifier
pub struct Query<E: Engine, O: OracleGadget<E>> {
    pub values: Vec<AllocatedNum<E>>,
    pub proof: O::Proof,
    pub _marker: std::marker::PhantomData<O>,
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


impl<E: Engine, O: OracleGadget<E>> FromStream<E, OracleHeight> for SinglePolySetupData<E, O>
{
    fn from_stream<CS: ConstraintSystem<E>, I: Iterator<Item = Option<E::Fr>>>(
        mut cs: CS, 
        iter: &mut I,
        params: OracleHeight,
    ) -> Result<Self, SynthesisError> 
    {
        let setup_value = AllocatedNum::from_stream(cs.namespace(|| "setup value"), iter, ())?;
        let commitment = O::Commitment::from_stream(cs.namespace(|| "setup commitment"), iter, params)?;
        Ok(SinglePolySetupData { setup_value, commitment })
    }
}


impl<E: Engine, O: OracleGadget<E>> FromStream<E, (CosetSize, OracleHeight)> for Query<E, O> {

    fn from_stream<CS: ConstraintSystem<E>, I: Iterator<Item = Option<E::Fr>>>(
        mut cs: CS, 
        iter: &mut I,
        params: (CosetSize, OracleHeight),
    ) -> Result<Self, SynthesisError> {

        let coset_size = params.0;
        let height = params.1;

        let values = Vec::from_stream(cs.namespace(|| "query values"), iter, coset_size)?;
        let proof = O::Proof::from_stream(cs.namespace(|| "query proof"), iter, height)?;

        Ok(Query { values, proof, _marker: std::marker::PhantomData::<O> })
    }
}


impl<E: Engine, O: OracleGadget<E>> FromStream<E, OracleHeight> for RedshiftSetupPrecomputation<E, O> {

    fn from_stream<CS: ConstraintSystem<E>, I: Iterator<Item = Option<E::Fr>>>(
        mut cs: CS, 
        iter: &mut I,
        params: OracleHeight,
    ) -> Result<Self, SynthesisError> 
    {
        let setup_point = AllocatedNum::from_stream(cs.namespace(|| "setup value"), iter, ())?;
        // q_l, q_r, q_o, q_m, q_c, q_add_sel, s_id, sigma_1, sigma_2, sigma_3
        let labels = ["q_l", "q_r", "q_o", "q_m", "q_c", "q_add_sel", "s_id", "sigma_1", "sigma_2", "sigma_3"];
        let mut data = Vec::with_capacity(labels.len());

        for label in labels.iter() {
            let elem = Labeled::new(
                label, 
                SinglePolySetupData::from_stream(cs.namespace(|| "setup data"), iter, params)?,
            );
            data.push(elem);
        }
        
        Ok(RedshiftSetupPrecomputation {setup_point, data})
    }
}


impl<E: Engine, O: OracleGadget<E>> FromStream<E, FriParams> for FriSingleQueryRoundData<E, O> {

    fn from_stream<CS: ConstraintSystem<E>, I: Iterator<Item = Option<E::Fr>>>(
        mut cs: CS, 
        iter: &mut I,
        fri_params: FriParams,
    ) -> Result<Self, SynthesisError> 
    {
        let coset_size = 1 << fri_params.collapsing_factor;
        let top_level_oracle_size = (fri_params.initial_degree_plus_one.get() * fri_params.lde_factor) / coset_size;
        let top_leve_height = log2_floor(top_level_oracle_size);
        
        let mut num_of_iters = log2_floor(fri_params.initial_degree_plus_one.get() / fri_params.final_degree_plus_one) / fri_params.collapsing_factor;
        // we do not count the very first and the last iterations
        num_of_iters -= 2;

        let labels = ["q_l", "q_r", "q_o", "q_m", "q_c", "q_add_sel", "s_id", "sigma_1", "sigma_2", "sigma_3",
            "a", "b", "c", "z_1", "z_2", "t_low", "t_mid", "t_high"];
        
        let mut upper_layer_queries = Vec::with_capacity(labels.len());

        for label in labels.iter() {
            let elem = Labeled::new(
                label, 
                Query::from_stream(cs.namespace(|| "upper_layer_query"), iter, (coset_size, top_leve_height))?,
            );
            upper_layer_queries.push(elem);
        }

        let mut cur_height = top_leve_height - fri_params.collapsing_factor;
        let mut queries = Vec::with_capacity(num_of_iters);

        for _ in 0..num_of_iters {
            let query = Query::from_stream(
                cs.namespace(|| "intermidiate query"), 
                iter, 
                (coset_size, cur_height),
            )?;
            cur_height -= fri_params.collapsing_factor;
            queries.push(query)
        }

        Ok(FriSingleQueryRoundData{ upper_layer_queries, queries })
    }
}


impl<E: Engine, O: OracleGadget<E>> FromStream<E, FriParams> for BatchedFriProof<E, O> {

    fn from_stream<CS: ConstraintSystem<E>, I: Iterator<Item = Option<E::Fr>>>(
        mut cs: CS, 
        iter: &mut I,
        fri_params: FriParams,
    ) -> Result<Self, SynthesisError> 
    {

        let coset_size = 1 << fri_params.collapsing_factor;
        let top_level_oracle_size = (fri_params.initial_degree_plus_one.get() * fri_params.lde_factor) / coset_size;
        let top_leve_height = log2_floor(top_level_oracle_size);
        
        let mut num_of_iters = log2_floor(fri_params.initial_degree_plus_one.get() / fri_params.final_degree_plus_one) / fri_params.collapsing_factor;
        // we do not count the very first and the last iterations
        num_of_iters -= 2;

        let mut cur_height = top_leve_height - fri_params.collapsing_factor;
        let mut commitments = Vec::with_capacity(num_of_iters);

        for _ in 0..num_of_iters {
            let commitment = O::Commitment::from_stream(
                cs.namespace(|| "intermidiate commitment"), 
                iter, 
                cur_height,
            )?;
            commitments.push(commitment);
            cur_height -= fri_params.collapsing_factor;
        }

        let final_coefficients = 
            Vec::from_stream(cs.namespace(|| "final coefficients"), iter, fri_params.final_degree_plus_one)?;

        let mut fri_round_queries = Vec::with_capacity(fri_params.R);
        for _ in 0..fri_params.R {
            let fri_round = FriSingleQueryRoundData::from_stream(
                cs.namespace(|| "FRI round query"), iter, fri_params.clone())?;
            fri_round_queries.push(fri_round);
        }
        
        Ok(BatchedFriProof { commitments, final_coefficients, fri_round_queries })
    }
}


impl<E: Engine, O: OracleGadget<E>> FromStream<E, FriParams> for RedshiftProof<E, O> {

    fn from_stream<CS: ConstraintSystem<E>, I: Iterator<Item = Option<E::Fr>>>(
        mut cs: CS, 
        iter: &mut I,
        fri_params: FriParams,
    ) -> Result<Self, SynthesisError> 
    {
              
        // containes opening values for:
        // a, b, c, c_shifted, q_l, q_r, q_o, q_m, q_c, q_add_sel, 
        // s_id, sigma_1, sigma_2, sigma_3,
        // z_1, z_2, z_1_shifted, z_2_shifted, t_low, t_mid, t_high
        let labels = ["a", "b", "c", "c_shifted", "q_l", "q_r", "q_o", "q_m", "q_c", "q_add_sel", 
            "s_id", "sigma_1", "sigma_2", "sigma_3", "z_1", "z_2", "z_1_shifted", "z_2_shifted",
            "t_low", "t_mid", "t_high"];

        let mut opening_values = Vec::with_capacity(labels.len());

        for label in labels.iter() {
            let elem = Labeled::new(
                label,
                AllocatedNum::from_stream(cs.namespace(|| "opening values"), iter, ())?,
            );
        
            opening_values.push(elem);
        }

        let coset_size = 1 << fri_params.collapsing_factor;
        let top_level_oracle_size = (fri_params.initial_degree_plus_one.get() * fri_params.lde_factor) / coset_size;
        let height = log2_floor(top_level_oracle_size);

        // contains commitments for a, b, c, z_1, z_2, t_low, t_mid, t_high
        let labels = ["a", "b", "c", "z_1", "z_2", "t_low", "t_mid", "t_high"];
        let mut commitments = Vec::with_capacity(labels.len());
        for label in labels.iter() {
            let elem = Labeled::new(
                label,
                O::Commitment::from_stream(cs.namespace(|| "commitments to witness polys"), iter, height)?,
            );
            commitments.push(elem);
        }

        let fri_proof = BatchedFriProof::from_stream(
            cs.namespace(|| "batched FRI proof"), 
            iter, 
            fri_params,
        )?;

        Ok(RedshiftProof { opening_values, commitments, fri_proof })
    }
}
