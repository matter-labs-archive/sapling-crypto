#![allow(non_snake_case)]

use bellman::redshift::IOP::hashes::rescue::{RescueParams};

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

use crate::circuit::num::*;


pub trait RescueSbox<E: Engine>: Clone + Copy {

    fn new() -> Self;

    fn rescue_alpha<CS : ConstraintSystem<E>>(elem: &Num<E>, cs: CS) -> Result<Num<E>, SynthesisError>;

    fn rescue_inalpha<CS : ConstraintSystem<E>>(elem: &Num<E>, cs: CS) -> Result<Num<E>, SynthesisError>;
}


fn mds<E: Engine, Params: RescueParams<E::Fr>>(
    in_state: &[Num<E>],
    params: &Params,
) -> Vec<Num<E>> {
    let mut out_state = vec![];
    let mds_matrix = params.get_mds_matrix();
    let RESCUE_M = params.t();
    
    for i in 0..RESCUE_M {
        let mut res = Num::zero();
        for j in 0..RESCUE_M {
            let mut temp = in_state[j].clone();
            temp.scale(mds_matrix[i][j]);
            res.add_assign(&temp);
        }
        out_state.push(res);
    }
    out_state
}


fn rescue_f<E: Engine, CS: ConstraintSystem<E>, Params: RescueParams<E::Fr>, SBOX: RescueSbox<E>>(
    cs: &mut CS,
    state: &mut [Num<E>],
    params: &Params,
) -> Result<(), SynthesisError> {

    let RESCUE_M = params.t();
    let RESCUE_ROUNDS = params.get_num_rescue_rounds();
    let constants = params.get_constants();
   
    for i in 0..RESCUE_M {
        state[i].add_assign(&Num::from_constant(&constants[0][i], &cs));
    }

    for r in 0..2 * RESCUE_ROUNDS {

        for entry in state.iter_mut() {
            if r % 2 == 0 {
                *entry = SBOX::rescue_inalpha(&entry, cs.namespace(|| "sbox inalpha"))?;
            }
            else {
                *entry = SBOX::rescue_alpha(&entry, cs.namespace(|| "sbox alpha"))?;
            }
        }

        for (input, output) in  mds::<E, Params>(state, params).into_iter().zip(state.iter_mut()) {
            *output = input;
        }
        for i in 0..RESCUE_M {
            state[i].add_assign(&Num::from_constant(&(constants[r + 1][i]), &cs));
        }
    }

    Ok(())
}

fn pad<E: Engine, CS: ConstraintSystem<E>, Params: RescueParams<E::Fr>>(
    input: &mut Vec<Num<E>>,
    cs: &mut CS,
    params: &Params,
) {

    let SPONGE_RATE = params.r();
    let magic_constant = params.padding_constant();
    let range = SPONGE_RATE - input.len();

    // apply necessary padding
    input.extend((0..range).map(|_| Num::from_constant(magic_constant, &cs))); 
}

fn rescue_duplex<E: Engine, CS: ConstraintSystem<E>, Params: RescueParams<E::Fr>, SBOX: RescueSbox<E>>(
    state: &mut Vec<Num<E>>,
    input: &mut Vec<Num<E>>,
    mut cs: CS,
    params: &Params,
) -> Result< Vec<Option<Num<E>>>, SynthesisError> {

    let SPONGE_RATE = params.r();
    let OUTPUT_RATE = params.c();
    pad(input, &mut cs, params);

    for i in 0..SPONGE_RATE {
        state[i].add_assign(&input[i]);
    }

    rescue_f::<E, CS, Params, SBOX>(&mut cs, state, params)?;

    let mut output = vec![];
    for i in 0..OUTPUT_RATE {
        output[i] = Some(state[i].clone());
    }

    Ok(output)
}

enum SpongeState<E: Engine> {
    Absorbing(Vec<Num<E>>),
    Squeezing(Vec<Option<Num<E>>>),
}

impl<E: Engine> SpongeState<E> {
    fn absorb(val: Num<E>) -> Self {
        SpongeState::Absorbing(vec![val])
    }

    fn default() -> Self {
        SpongeState::Absorbing(vec![])
    }
}


pub struct RescueGadget<E: Engine, RP: RescueParams<E::Fr>, SBOX: RescueSbox<E>> {
    sponge: SpongeState<E>,
    state: Vec<Num<E>>,
    _params_marker: std::marker::PhantomData<RP>,
    _sbox_marker: std::marker::PhantomData<SBOX>,
}


impl<E: Engine, RP: RescueParams<E::Fr>, SBOX: RescueSbox<E>> RescueGadget<E, RP, SBOX> {

    pub fn new(params: &RP) -> Self {
        
        let RESCUE_M = params.t();
        let state = (0..RESCUE_M).map(|_| Num::zero()).collect();

        RescueGadget {
            sponge: SpongeState::Absorbing(vec![]),
            state,
            _params_marker: std::marker::PhantomData::<RP>,
            _sbox_marker: std::marker::PhantomData::<SBOX>,
        }
    }
   
    pub fn absorb<CS: ConstraintSystem<E>>(&mut self, val: AllocatedNum<E>, mut cs: CS, params: &RP) -> Result<(), SynthesisError> {
        let SPONGE_STATE = params.r();
        let val = val.into();
        match self.sponge {
            SpongeState::Absorbing(ref mut input) => {
                if input.len() < SPONGE_STATE {
                    input.push(val);
                    return Ok(());
                }

                // We've already absorbed as many elements as we can
                rescue_duplex::<E, _, RP, SBOX>(&mut self.state, input, cs.namespace(|| "rescue duplex"), params)?;
                self.sponge = SpongeState::absorb(val);
            }
            SpongeState::Squeezing(_) => {
                // Drop the remaining output elements
                self.sponge = SpongeState::absorb(val);
            }
        }

        Ok(())
    }

    pub fn squeeze<CS: ConstraintSystem<E>>(&mut self, mut cs: CS, params: &RP) -> Result<Num<E>, SynthesisError> {
        loop {
            match self.sponge {
                SpongeState::Absorbing(ref mut input) => {
                    self.sponge = SpongeState::Squeezing(rescue_duplex::<E, _, RP, SBOX>(
                        &mut self.state,
                        input,
                        cs.namespace(|| "rescue duplex"),
                        params,
                    )?);
                }
                SpongeState::Squeezing(ref mut output) => {
                    for entry in output.iter_mut() {
                        if let Some(e) = entry.take() {
                            //e.simplify(cs.namespace(|| "simplification"))
                            return Ok(e)
                        }
                    }
                    // We've already squeezed out all available elements
                    unreachable!("Sponge number is too small");
                    //self.sponge = SpongeState::Absorbing(vec![]);
                }
            }
        }
    }
}


#[cfg(test)]
mod test {
    use super::*;
    use bellman::Circuit;
    use bellman::redshift::IOP::hashes::rescue::{Rescue, RescueParams};
    use bellman::redshift::IOP::hashes::rescue::bn256_rescue_params::BN256Rescue;

    use bellman::pairing::bn256::Fr as Fr;
    use bellman::pairing::bn256::Bn256;

    use super::super::bn256_rescue_sbox::BN256RescueSbox;
    use crate::circuit::test::TestConstraintSystem;

    #[test]
    fn test_rescue_gadget() {
        struct TestCircuit<E: Engine, RP: RescueParams<E::Fr>, SBOX: RescueSbox<E>> {
            params: RP,
            sbox: SBOX,
            inputs: Vec<E::Fr>,
            expected_outputs: Vec<E::Fr>,
        }

        impl<E: Engine, RP: RescueParams<E::Fr>, SBOX: RescueSbox<E>> Circuit<E> for TestCircuit<E, RP, SBOX> {
            fn synthesize<CS: ConstraintSystem<E>>(
                self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {

                let mut g = RescueGadget::<E, RP, SBOX>::new(&self.params);

                assert!(self.inputs.len() <= self.params.r());
                assert!(self.expected_outputs.len() <= self.params.c());

                for elem in self.inputs.into_iter() {
                    let val = AllocatedNum::alloc(cs.namespace(|| "rescue test input"), || Ok(elem))?;
                    g.absorb(val.into(),  cs.namespace(|| "absorb input"), &self.params)?;
                }

                for elem in self.expected_outputs.into_iter() {
                    let val = AllocatedNum::alloc_input(cs.namespace(|| "rescue output"), || Ok(elem))?;
                    let s = g.squeeze(cs.namespace(|| "squeeze s"), &self.params)?;
                    cs.enforce(
                        || "check output", 
                        |lc| lc + s.get_lc(), 
                        |lc| lc + CS::one(),
                        |lc| lc + val.get_variable(),
                    );
                }

                Ok(())
            }
        }

        let bn256_rescue_params = BN256Rescue::default();
        let mut r = Rescue::new(&bn256_rescue_params);

        // construct 3 and 9 as inputs
        let mut a = Fr::one();
        a.double();
        a.add_assign(&Fr::one());

        let mut b = a.clone();
        b.double();

        let inputs = vec![a, b]; 

        r.absorb(a, &bn256_rescue_params);
        r.absorb(b, &bn256_rescue_params);

        let expected_s = r.squeeze(&bn256_rescue_params);

        let test_circuit = TestCircuit::<Bn256, BN256Rescue, BN256RescueSbox> {
            params: bn256_rescue_params,
            sbox: BN256RescueSbox{},
            inputs: inputs,
            expected_outputs: vec![expected_s],
        };

        let mut cs = TestConstraintSystem::<Bn256>::new();
        test_circuit.synthesize(&mut cs).expect("should synthesize");

        assert!(cs.is_satisfied());

        println!("Rescue 2->1 with 22 rounds requires {} constraints", cs.num_constraints());
    }    
}









