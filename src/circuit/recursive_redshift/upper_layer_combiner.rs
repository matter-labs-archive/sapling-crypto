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
use crate::circuit::recursive_redshift::oracles::OracleGadget;

// given an evaluation point x and auxiliarly point x_1,
// aggregation_challenge = alpha (the final value of alpha is also returned!)
// and an array of pairs (f_i(x), f_i(x_1)) - one pair for each polynomial f_i(t) in question (i \in [0, 1, .., n])
// this function computes: 
// y = /sum alpha^i [f_i(x) - f_i(x_1)]/ [x - x_1]
// and returns the pair (y, final_alpha)

fn combine_at_single_point<E: Engine, CS: ConstraintSystem<E>>(
    cs : &mut CS,
    pairs: Vec<(AllocatedNum<E>, AllocatedNum<E>)>, 
    x: &Num<E>, 
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
    let mut temp : Num<E> = x.clone();
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
    x: &Num<E>, 
    x_1: AllocatedNum<E>,
    x_2: AllocatedNum<E>, 
    alpha: AllocatedNum<E>,
) -> Result<(AllocatedNum<E>, AllocatedNum<E>), SynthesisError> 
{
    
    // precompute the common slope
    let mut slope : Num<E> = x.clone();
    slope -= x_1.clone();
    let mut slope_denum : Num<E> = x_2.clone().into();
    slope_denum -= x_1.clone();
    
    slope = Num::mul(cs.namespace(|| ""), &slope, &slope_denum)?.into();

    let mut res = Num::zero(); 
    let mut aggr_mult = alpha.clone();

    for (f_x, f_x_1, f_x_2) in triples.into_iter() {

        //evaluate interpolation poly -U_i(x) = -f_x_1 - slope * (f_x_2 - f_x_1) = slope * (f_x_1 - f_x_2) - f_x_1
        let mut temp : Num<E> = f_x_1.clone().into();
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
    t_0 += x_2.clone();
    let t_0 = Num::mul(cs.namespace(|| ""), &t_0, &x)?;
    let t_1 = x_1.mul(cs.namespace(|| ""), &x_2)?;

    let mut common_denominator : Num<E> = Num::mul(cs.namespace(|| ""), &x, &x)?.into(); 
    common_denominator -= t_0;
    common_denominator += t_1;
    
    let res = Num::div(cs.namespace(|| ""), &res, &common_denominator)?;
    Ok((res, aggr_mult))
}


pub fn find_setup_value_by_label<E: Engine, I: OracleGadget<E>>(
    label: Label, 
    arr: &Vec<Labeled<SinglePolySetupData<E, I>>>,
) -> Result<AllocatedNum<E>, SynthesisError>
{
    arr.iter().find(|elem| elem.label == label).map(|elem| elem.data.setup_value.clone()).ok_or(SynthesisError::Unknown)
}


pub fn upper_layer_combiner_impl<E: Engine, I: OracleGadget<E>, CS: ConstraintSystem<E>>(
    mut cs: CS,
    domain_values: Vec<Labeled<&AllocatedNum<E>>>,
    evaluation_point : &Num<E>,
    setup_precomp: &RedshiftSetupPrecomputation<E, I>,
    opening_values: &LabeledVec<AllocatedNum<E>>,
    z: AllocatedNum<E>,
    aggr_challenge : AllocatedNum<E>,
    omega: &E::Fr,
) -> Result<AllocatedNum<E>, SynthesisError> 
{
    let setup_polys = &setup_precomp.data;
    
    // combine polynomials a, b, t_low, t_mid, t_high,
    // which are opened only at z
    let pairs : Vec<(AllocatedNum<E>, AllocatedNum<E>)> = vec![
        (find_by_label("a", &domain_values)?.clone(), find_by_label("a", opening_values)?.clone()),
        (find_by_label("b", &domain_values)?.clone(), find_by_label("b", opening_values)?.clone()),
        (find_by_label("t_low", &domain_values)?.clone(), find_by_label("t_low", opening_values)?.clone()),
        (find_by_label("t_mid", &domain_values)?.clone(), find_by_label("t_mid", opening_values)?.clone()),
        (find_by_label("t_high", &domain_values)?.clone(), find_by_label("t_high", opening_values)?.clone()),
    ];
       
    let (res1, alpha1) = combine_at_single_point(
        &mut cs, pairs, &evaluation_point, z.clone(), aggr_challenge.clone())?;

    // combine witness polynomials z_1, z_2, c which are opened at z and z * omega

    let temp = Num::from_constant(omega, &cs);
    let z_shifted = Num::mul_by_var_with_coeff(cs.namespace(|| ""), &temp, &z, E::Fr::one())?;

    let witness_triples : Vec<(AllocatedNum<E>, AllocatedNum<E>, AllocatedNum<E>)> = vec![
        ( find_by_label("z_1", &domain_values)?.clone(), 
          find_by_label("z_1", opening_values)?.clone(), 
          find_by_label("z_1_shifted", opening_values)?.clone() ),

        ( find_by_label("z_2", &domain_values)?.clone(), 
          find_by_label("z_2", opening_values)?.clone(), 
          find_by_label("z_2_shifted", opening_values)?.clone() ),

        ( find_by_label("c", &domain_values)?.clone(), 
          find_by_label("c", opening_values)?.clone(), 
          find_by_label("c_shifted", opening_values)?.clone() ),
    ];

    let (res2, alpha2) = combine_at_two_points(
        &mut cs, witness_triples, &evaluation_point, z.clone(), z_shifted.clone(), aggr_challenge.clone())?;

    // finally combine setup polynomials q_l, q_r, q_o, q_m, q_c, q_add_sel, s_id, sigma_1, sigma_2, sigma_3
    // which are opened at z and z_setup
    // in current implementation we assume that setup point is the same for all circuit-defining polynomials!

    let setup_triples : Vec<(AllocatedNum<E>, AllocatedNum<E>, AllocatedNum<E>)> = vec![
        ( find_by_label("q_l", &domain_values)?.clone(), 
          find_by_label("q_l", opening_values)?.clone(), 
          find_setup_value_by_label("q_l", setup_polys)? ),

        ( find_by_label("q_r", &domain_values)?.clone(), 
          find_by_label("q_r", opening_values)?.clone(), 
          find_setup_value_by_label("q_r", setup_polys)? ),

        ( find_by_label("q_o", &domain_values)?.clone(), 
          find_by_label("q_o", opening_values)?.clone(), 
          find_setup_value_by_label("q_o", setup_polys)? ),

        ( find_by_label("q_m", &domain_values)?.clone(), 
          find_by_label("q_m", opening_values)?.clone(), 
          find_setup_value_by_label("q_m", setup_polys)? ),

        ( find_by_label("q_c", &domain_values)?.clone(), 
          find_by_label("q_c", opening_values)?.clone(), 
          find_setup_value_by_label("q_c", setup_polys)? ),

        ( find_by_label("q_add_sel", &domain_values)?.clone(), 
          find_by_label("q_add_sel", opening_values)?.clone(), 
          find_setup_value_by_label("q_add_sel", setup_polys)? ),

        ( find_by_label("s_id", &domain_values)?.clone(), 
          find_by_label("s_id", opening_values)?.clone(), 
          find_setup_value_by_label("s_id", setup_polys)? ),

        ( find_by_label("sigma_1", &domain_values)?.clone(), 
          find_by_label("sigma_l", opening_values)?.clone(), 
          find_setup_value_by_label("sigma_l", setup_polys)? ),

        ( find_by_label("sigma_2", &domain_values)?.clone(), 
          find_by_label("sigma_2", opening_values)?.clone(), 
          find_setup_value_by_label("sigma_2", setup_polys)? ),

        ( find_by_label("sigma_3", &domain_values)?.clone(), 
          find_by_label("sigma_3", opening_values)?.clone(), 
          find_setup_value_by_label("sigma_3", setup_polys)? ),
    ];

    let common_setup_point = setup_precomp.setup_point.clone();

    let (res3, _) = combine_at_two_points(
        &mut cs, setup_triples, &evaluation_point, z, common_setup_point, aggr_challenge)?;

    // res = res1 + res2 * alpha_1 + res3 * alpha_1 * alpha_2
    // we constraint it in the form res - res1 = alpha_1 * (res2 + res3 * alpha2)
    let temp = res3.mul(cs.namespace(|| ""), &alpha2)?;
    
    let res = AllocatedNum::alloc(cs.namespace(|| ""), || {

        let mut res1 = res1.get_value().ok_or(SynthesisError::AssignmentMissing)?;
        let mut res2 = res2.get_value().ok_or(SynthesisError::AssignmentMissing)?;
        let mut res3 = res3.get_value().ok_or(SynthesisError::AssignmentMissing)?;
        let mut alpha1 = alpha1.get_value().ok_or(SynthesisError::AssignmentMissing)?;
        let alpha2 = alpha2.get_value().ok_or(SynthesisError::AssignmentMissing)?;

        res2.mul_assign(&alpha1);
        res1.add_assign(&res2);
        alpha1.mul_assign(&alpha2);
        res3.mul_assign(&alpha1);
        res1.add_assign(&res3);

        Ok(res1)
    })?;

    cs.enforce(
        || "",        
        |lc| lc + alpha1.get_variable(),
        |lc| lc + res2.get_variable() + temp.get_variable(),
        |lc| lc + res.get_variable() - res1.get_variable(), 
    );

    Ok(res)
}


pub trait UpperLayerCombiner<E: Engine> {
    fn combine<CS: ConstraintSystem<E>>(
        &self,
        cs: CS, 
        domain_values: Vec<Labeled<&AllocatedNum<E>>>,
        evaluation_point : &Num<E>
    ) -> Result<AllocatedNum<E>, SynthesisError>; 
}


pub struct ReshiftCombiner<E: Engine, I: OracleGadget<E>> {
    pub setup_precomp: RedshiftSetupPrecomputation<E, I>,
    pub opening_values: LabeledVec<AllocatedNum<E>>,
    pub z: AllocatedNum<E>,
    pub aggr_challenge : AllocatedNum<E>,
    pub omega: E::Fr,
}

impl<E: Engine, I: OracleGadget<E>> UpperLayerCombiner<E> for ReshiftCombiner<E, I> {

    fn combine<CS: ConstraintSystem<E>>(
        &self,
        cs: CS, 
        domain_values: Vec<Labeled<&AllocatedNum<E>>>,
        evaluation_point : &Num<E>
    ) -> Result<AllocatedNum<E>, SynthesisError>
    {
        upper_layer_combiner_impl(
            cs,
            domain_values,
            evaluation_point,
            &self.setup_precomp,
            &self.opening_values,
            self.z.clone(),
            self.aggr_challenge.clone(),
            &self.omega,
        )
    }
}


