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


// this trais is used as an abstraction over Merklee proofs

pub trait OracleGadget<E: Engine> {
    type Params;
    // additional paramter for parser is the height of the tree
    type Proof : FromStream<E, OracleHeight>;
    type Commitment : FromStream<E, OracleHeight>;

    fn new(params: &Self::Params) -> Self;

    fn validate<CS: ConstraintSystem<E>>(
        &self, 
        cs: CS,
        height: usize, 
        elems : &[AllocatedNum<E>],
        path: &[Boolean],
        commitment: &Self::Commitment, 
        proof: &Self::Proof,
    ) -> Result<Boolean, SynthesisError>;
}


