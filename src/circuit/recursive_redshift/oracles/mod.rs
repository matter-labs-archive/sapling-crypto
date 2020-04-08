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
    LinearCombination,
    Variable
};

use std::marker::PhantomData;

use crate::circuit::num::*;
use crate::circuit::boolean::*;
use crate::circuit::recursive_redshift::data_structs::*;

pub mod rescue_merklee_proof;




pub fn log2_floor(num: usize) -> usize {
    assert!(num > 0);
    let mut pow: usize = 0;

    while (1 << (pow+1)) <= num {
        pow += 1;
    }
    pow
}

// this trais is used as an abstraction over Merklee proofs

pub trait OracleGadget<E: Engine> {
    type Params;
    // additional paramter for parser is the height of the tree
    type Proof : FromStream<E, usize>;
    type Commitment : FromStream<E, usize>;

    fn new(params: &Self::Params) -> Self;

    fn validate<CS: ConstraintSystem<E>>(
        &self, 
        cs: CS,
        height: usize, 
        elems : &[Num<E>],
        path: &[Boolean],
        commitment: &Self::Commitment, 
        proof: &Self::Proof,
    ) -> Result<Boolean, SynthesisError>;
}

// container that holds the values alongside the proof 
// NB: there is no need to store the index (or path), as it is calculated and checked by verifier
pub struct Query<E: Engine, O: OracleGadget<E>> {
    pub values: Vec<Num<E>>,
    pub proof: O::Proof,
    pub _marker: std::marker::PhantomData<O>,
}


