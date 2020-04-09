use bellman::pairing::{
    Engine,
};

use bellman::pairing::ff::{
    Field,
    PrimeField,
};

use bellman::{
    ConstraintSystem,
    SynthesisError,
};

use crate::circuit::num::*;
use crate::circuit::boolean::*;
use crate::circuit::recursive_redshift::data_structs::*;

// given an evaluation point x and auxiliarly point x_1,
// aggregation_challenge = alpha (the final value of alpha is also returned!)
// and an array of pairs (f_i(x), f_i(x_1)) - one pair for each polynomial f_i(t) in question (i \in [0, 1, .., n])
// this function computes: 
// y = /sum alpha^i [f_i(x) - f_i(x_1)]/ [x - x_1]
// and returns the pair (y, final_alpha)

fn combine_at_single_point<E: Engine, CS: ConstraintSystem<E>>(
    cs : &mut CS,
    pairs: Vec<(AllocatedNum<E>, AllocatedNum<E>)>, 
    x: AllocatedNum<E>, 
    x_1: AllocatedNum<E>, 
    alpha: AllocatedNum<E>,
) -> Result<(AllocatedNum<E>, AllocatedNum<E>), SynthesisError> 
{

    let mut res : Num<E> = Num::zero();
    let mut aggr_mult = alpha.clone();

    for (i, (a, b)) in pairs.into_iter().enumerate() {
        // separately compute numerators
        let mut temp : Num<E> = a.into();
        temp -= b;
        if i == 0 {
            res += &temp;
        }
        else {
            res += Num::mul(cs.namespace(|| ""), &temp, &aggr_mult.clone().into())?;
            aggr_mult = aggr_mult.mul(cs.namespace(|| ""), &alpha)?;
        }    
    }

    // now compute the common denominator
    let mut temp : Num<E> = x.into();
    temp -= &x_1.into();
    let res = Num::div(cs.namespace(|| ""), &res, &temp)?;
    
    Ok((res, aggr_mult))
}