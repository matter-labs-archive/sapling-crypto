// we prefer to make it modular and generic as we have to use sha256-based channel instead of rescue_channel in future releases
use crate::circuit::num::*;
use bellman::pairing::{
    Engine,
};
use bellman::{
    SynthesisError,
    ConstraintSystem,
};

pub mod rescue_channel;


pub trait ChannelGadget<E: Engine> {
    type Params;

    fn new(params: Self::Params) -> Self;

    fn consume<CS: ConstraintSystem<E>>(&mut self, data: AllocatedNum<E>, cs: CS) -> Result<(), SynthesisError>;
    fn produce_challenge<CS: ConstraintSystem<E>>(&mut self, cs: CS) -> Result<AllocatedNum<E>, SynthesisError>;
}