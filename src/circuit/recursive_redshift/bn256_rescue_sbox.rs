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
use super::rescue::RescueSbox;
use bellman::redshift::IOP::hashes::rescue::{RescueParams};
use bellman::redshift::IOP::hashes::rescue::bn256_rescue_params::BN256Rescue;
use bellman::pairing::bn256::Bn256 as E;
use bellman::pairing::bn256::Fr as Fr;


struct BN256RescueSbox;

impl BN256RescueSbox {

    fn constrain_rescue_pow_bn256<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        input_var: &LinearCombination<E>,
        output_var: &LinearCombination<E>,
        x: Option<Fr>,
    ) -> Result<(), SynthesisError>
    {
        let x2 = x.and_then(|x| {
            let mut temp = x;
            temp.square();
            Some(temp)
        });

        let x4 = x2.and_then(|x| {
            let mut temp = x;
            temp.square();
            Some(temp)
        });

        let x5 = match (x4, x) {
            (Some(a), Some(b)) => {
                let mut temp = a;
                temp.mul_assign(&b);
                Some(temp)
            }
            (_, _) => None
        };

        let x2_var = cs.alloc(|| "x^2", || x2.ok_or(SynthesisError::AssignmentMissing))?;
        let x4_var = cs.alloc(|| "x^4", || x4.ok_or(SynthesisError::AssignmentMissing))?;

        cs.enforce(
            || "x * x == x^2",
            |lc| lc + input_var,
            |lc| lc + input_var,
            |lc| lc + x2_var,
        );

        cs.enforce(
            || "x^2 * x^2 == x^4",
            |lc| lc + x2_var,
            |lc| lc + x2_var,
            |lc| lc + x4_var,
        );

        cs.enforce(
            || "x^4 * x == x^5",
            |lc| lc + x4_var,
            |lc| lc + input_var,
            |lc| lc + output_var,
        );

        Ok(())
    }
}

impl RescueSbox<E> for BN256RescueSbox {

    fn rescue_alpha<CS : ConstraintSystem<E>>(elem: &Num<E>, mut cs: CS) -> Result<Num<E>, SynthesisError> {

        #![allow(non_snake_case)]       
        let RESCUE_ALPHA : u64 = 5;
        
        let base_value = elem.get_value();
        let base_lc = elem.get_lc();

        let result_value = base_value.and_then(|num| Some(num.pow(&[RESCUE_ALPHA])));
        let resut_var_alloc = AllocatedNum::alloc(
            cs.namespace(|| "rescue_alpha_sbox"), 
            || result_value.ok_or(SynthesisError::AssignmentMissing)
        )?;
        let result_var : Num<E> = resut_var_alloc.into();

        Self::constrain_rescue_pow_bn256(&mut cs, base_lc, result_var.get_lc(), base_value)?;
        Ok(result_var)
    }

    fn rescue_inalpha<CS : ConstraintSystem<E>>(elem: &Num<E>, mut cs: CS) -> Result<Num<E>, SynthesisError> {

        #![allow(non_snake_case)]
        let RESCUE_INALPHA : [u64; 4] = [14981214993055009997, 6006880321387387405, 10624953561019755799, 2789598613442376532];

        let result_value = elem.get_value();
        let result_lc = elem.get_lc();

        let base_value = result_value.and_then(|num| Some(num.pow(&RESCUE_INALPHA)));
        let base_var_alloc = AllocatedNum::alloc(
            cs.namespace(|| "rescue_inalpha_sbox"), 
            || base_value.ok_or(SynthesisError::AssignmentMissing)
        )?;
        let base_var : Num<E> = base_var_alloc.into();

        Self::constrain_rescue_pow_bn256(&mut cs, base_var.get_lc(), result_lc, base_value)?;
        Ok(base_var)

    }
}