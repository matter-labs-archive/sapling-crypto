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
    temp -= x_1;
    let res = Num::div(cs.namespace(|| ""), &res, &temp)?;
    
    Ok((res, aggr_mult))
}


// given an evaluation point x and two auxiliarly points x_1, x_2,
// aggregation_challenge = alpha (the final value of alpha is also returned!)
// and an array of triples (f_i(x), f_i(x_1), f_i(x_2)) - one triple for each polynomial f_i(t) in question (i \in [0, 1, .., n])
// this function computes: 
// y = /sum alpha^i [f_i(x) - U_i(x)]/ [(x - x_1)(x - x_2)]
// where U_i(t) is the unique linear function, having value f_i(x_1) at x_1 and f_i(x_2) at x_2
// note that such U_i(t) = f_i(x_1) + [t - x_1]/ [x_2 - x_1] (f_i(x_2) - f_i(x_1))  and hence
// U_i(x) = f_i(x_1) + [x - x_1]/ [x_2 - x_1] (f_i(x_2) - f_i(x_1))
// this means that all U_i(x) share the common slope [x - x_1] / [x_2 - x_1]
// which therefore may be precomputed once and forall
// funtion returns the pair (y, final_alpha)

fn combine_at_two_points<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    triples: Vec<(AllocatedNum<E>, AllocatedNum<E>, AllocatedNum<E>)>, 
    x: AllocatedNum<E>, 
    x_1: AllocatedNum<E>,
    x_2: AllocatedNum<E>, 
    alpha: AllocatedNum<E>,
) -> Result<(AllocatedNum<E>, AllocatedNum<E>), SynthesisError> 
{
    
    // precompute the common slope
    let mut slope : Num<E> = x.into();
    slope -= x_1;
    let mut slope_denum : Num<E> = x_2.into();
    slope_denum -= x_1;
    
    slope = Num::mul(cs.namespace(|| ""), &slope, &slope_denum)?.into();

    let mut res = Num::zero(); 
    let mut aggr_mult = alpha.clone();

    for (f_x, f_x_1, f_x_2) in triples.into_iter() {

        //evaluate interpolation poly -U_i(x) = -f_x_1 - slope * (f_x_2 - f_x_1) = slope * (f_x_1 - f_x_2) - f_x_1
        let mut temp : Num<E> = f_x_1.into();
        temp -= f_x_2;
        temp = Num::mul(cs.namespace(|| ""), &temp, &slope)?.into();
        temp -= f_x_1;

        // compute nominator: aggr_mult * (f_x - U_i(x))
        temp += f_x;
        temp = Num::mul_by_var_with_coeff(cs.namespace(|| ""), &temp, &aggr_mult, E::Fr::one())?.into();
        
        res += &temp;
        aggr_mult = aggr_mult.mul(cs.namespace(|| ""), &alpha)?;
    }

    // now compute the common denominator
    // (x - x_1)(x - x_2) = x^2 - (x_1 + x_2) * x + x_1 * x_2
    let mut t_0 : Num<E> = x_1.clone().into();
    t_0 += x_2;
    let t_0 = Num::mul_by_var_with_coeff(cs.namespace(|| ""), &t_0, &x, E::Fr::one())?;
    let t_1 = x_1.mul(cs.namespace(|| ""), &x_2)?;

    let mut common_denominator : Num<E> = x.square(cs.namespace(|| ""))?.into(); 
    common_denominator -= t_0;
    common_denominator += t_1;
    
    let res = Num::div(cs.namespace(|| ""), &res, &common_denominator)?;
    Ok((res, aggr_mult))
}


pub fn upper_layer_combiner_impl<E: Engine, I: OracleGadget<E>, CS: ConstraintSystem<E>>(
    mut cs: CS,
    values: Vec<Labeled<&AllocatedNum<E>>>,
    ev_p : &Num<E>,
    RedshiftSetupPrecomputation,
    pub opening_values: LabeledVec<AllocatedNum<E>>
) -> Result<AllocatedNum<E>, SynthesisError> 
{
    

    

    // combine polynomials a, b, t_low, t_mid, t_high,
    // which are opened only at z
    let pairs : Vec<(&E::Fr, E::Fr)> = vec![
        (find_poly_value_at_omega("a", &arr)?, a_at_z),
        (find_poly_value_at_omega("b", &arr)?, b_at_z),
        (find_poly_value_at_omega("t_low", &arr)?, t_low_at_z),
        (find_poly_value_at_omega("t_mid", &arr)?, t_mid_at_z),
        (find_poly_value_at_omega("t_high", &arr)?, t_high_at_z),
    ];

    let (mut res1, mut alpha1) = combine_at_single_point(pairs, &evaluation_point, &z, &aggregation_challenge);

    // combine witness polynomials z_1, z_2, c which are opened at z and z * omega

    let mut z_shifted = z;
    z_shifted.mul_assign(&omega);

    let witness_triples : Vec<(&E::Fr, E::Fr, E::Fr)> = vec![
        (find_poly_value_at_omega("z_1", &arr)?, z_1_at_z, z_1_shifted_at_z),
        (find_poly_value_at_omega("z_2", &arr)?, z_2_at_z, z_2_shifted_at_z),
        (find_poly_value_at_omega("c", &arr)?, c_at_z, c_shifted_at_z),
    ];

    let (mut res2, alpha2) = combine_at_two_points(witness_triples, &evaluation_point, &z, &z_shifted, &aggregation_challenge);

    // finally combine setup polynomials q_l, q_r, q_o, q_m, q_c, q_add_sel, s_id, sigma_1, sigma_2, sigma_3
    // which are opened at z and z_setup
    // in current implementation we assume that setup point is the same for all circuit-defining polynomials!

    let setup_aux = vec![
        &setup_precomp.q_l_aux, &setup_precomp.q_r_aux, &setup_precomp.q_o_aux, &setup_precomp.q_m_aux, 
        &setup_precomp.q_c_aux, &setup_precomp.q_add_sel_aux, &setup_precomp.s_id_aux, &setup_precomp.sigma_1_aux, 
        &setup_precomp.sigma_2_aux, &setup_precomp.sigma_3_aux,
    ];
    assert!(setup_aux.windows(2).all(|w| w[0].setup_point == w[1].setup_point));
    let common_setup_point = setup_precomp.q_l_aux.setup_point;

    let setup_triples : Vec<(&E::Fr, E::Fr, E::Fr)> = vec![
        (find_poly_value_at_omega("q_l", &arr)?, q_l_at_z, setup_precomp.q_l_aux.setup_value),
        (find_poly_value_at_omega("q_r", &arr)?, q_r_at_z, setup_precomp.q_r_aux.setup_value),
        (find_poly_value_at_omega("q_o", &arr)?, q_o_at_z, setup_precomp.q_o_aux.setup_value),
        (find_poly_value_at_omega("q_m", &arr)?, q_m_at_z, setup_precomp.q_m_aux.setup_value),
        (find_poly_value_at_omega("q_c", &arr)?, q_c_at_z, setup_precomp.q_c_aux.setup_value),
        (find_poly_value_at_omega("q_add_sel", &arr)?, q_add_sel_at_z, setup_precomp.q_add_sel_aux.setup_value),
        (find_poly_value_at_omega("s_id", &arr)?, s_id_at_z, setup_precomp.s_id_aux.setup_value),
        (find_poly_value_at_omega("sigma_1", &arr)?, sigma_1_at_z, setup_precomp.sigma_1_aux.setup_value),
        (find_poly_value_at_omega("sigma_2", &arr)?, sigma_2_at_z, setup_precomp.sigma_2_aux.setup_value),
        (find_poly_value_at_omega("sigma_3", &arr)?, sigma_3_at_z, setup_precomp.sigma_3_aux.setup_value),
    ];

    let (mut res3, _) = combine_at_two_points(setup_triples, &evaluation_point, &z, &common_setup_point, &aggregation_challenge);

    // res = res1 + res2 * alpha_1 + res_3 * alpha_1 * alpha_2
    res2.mul_assign(&alpha1);
    res1.add_assign(&res2);
    alpha1.mul_assign(&alpha2);
    res3.mul_assign(&alpha1);
    res1.add_assign(&res3);

    Some(res1)
};


