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
    type Proof;
    type Commitment;

    fn new(params: Self::Params) -> Self;

    fn validate<CS: ConstraintSystem<E>>(
        &self, 
        cs: CS, 
        elems : &[Num<E>],
        path: &[Boolean],
        commitment: &Self::Commitment, 
        proof: &Self::Proof,
    ) -> Result<Boolean, SynthesisError>;
}


