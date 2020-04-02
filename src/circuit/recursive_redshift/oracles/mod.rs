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

// this trais is used as an abstraction over Merklee proofs

pub trait OracleGadget<E: Engine> {
    type Params;
    type Proof;
    type Commitment;

    fn new(params: Self::Params) -> Self;

    fn consume<CS: ConstraintSystem<E>>(&mut self, data: Num<E>, cs: CS) -> Result<(), SynthesisError>;
    fn produce_challenge<CS: ConstraintSystem<E>>(&mut self, cs: CS) -> Result<Num<E>, SynthesisError>;
}

