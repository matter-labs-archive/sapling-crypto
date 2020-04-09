use super::*;
use crate::circuit::recursive_redshift::hashes::rescue::{RescueGadget, RescueSbox};

use bellman::redshift::IOP::hashes::rescue::{Rescue, RescueParams};


pub struct RescueChannelGadget<'a, E: Engine, RP: RescueParams<E::Fr>, SBOX: RescueSbox<E>> {
    state: RescueGadget<E, RP, SBOX>,
    params: &'a RP,
}

impl<'a, E, RP, SBOX> ChannelGadget<E> for RescueChannelGadget<'a, E, RP, SBOX>
where E: Engine, RP: RescueParams<E::Fr>, SBOX: RescueSbox<E>
{
    type Params = &'a RP;

    fn new(channel_params: Self::Params) -> Self {
        Self {
            state: RescueGadget::<E, RP, SBOX>::new(channel_params),
            params: channel_params,
        }
    }

    fn consume<CS: ConstraintSystem<E>>(&mut self, data: AllocatedNum<E>, cs: CS) -> Result<(), SynthesisError> {      
        self.state.absorb(data, cs, self.params)
    }

    fn produce_challenge<CS: ConstraintSystem<E>>(&mut self, cs: CS) -> Result<AllocatedNum<E>, SynthesisError> {
        self.state.squeeze(cs, self.params)
    }
}