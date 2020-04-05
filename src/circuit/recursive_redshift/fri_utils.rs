use bellman::pairing::{
    Engine,
};
use bellman::{
    SynthesisError,
    ConstraintSystem,
};

use bellman::pairing::ff::{
    Field,
    PrimeField,
};
use bellman::redshift::domains::*;

use crate::circuit::num::*;
use crate::circuit::boolean::*;


pub struct FriUtilsGadget<E: Engine> {
    domain_size: usize,
    log_domain_size: usize,
    collapsing_factor: usize,
    wrapping_factor: usize,
    omega_inv: E::Fr,
    two: E::Fr,
    two_inv: E::Fr,
    _marker: std::marker::PhantomData<E>,
}


impl<E: Engine> FriUtilsGadget<E> {

    fn log2_floor(num: usize) -> usize {
        assert!(num > 0);
        let mut pow: usize = 0;

        while (1 << (pow+1)) <= num {
            pow += 1;
        }
        pow
    }

    pub fn get_domain_size(&self) -> usize {
        self.domain_size
    }

    pub fn get_log_domain_size(&self) -> usize {
        self.log_domain_size
    }

    //wrapping factor here is size of coset: 1 << collapsing_factor
    pub fn new(domain_size: usize, collapsing_factor: usize) -> Self {
        
        assert!(domain_size.is_power_of_two());
        let log_domain_size = Self::log2_floor(domain_size);

        let domain = Domain::<E::Fr>::new_for_size(domain_size as u64).expect("should construct");
        let omega = domain.generator;
        let omega_inv = omega.inverse().expect("should exist");

        let mut two = E::Fr::one();
        two.double();
        let two_inv = two.inverse().expect("should exist");

        FriUtilsGadget {
            domain_size,
            log_domain_size,
            collapsing_factor,
            wrapping_factor: 1<<collapsing_factor,
            omega_inv,
            two,
            two_inv,
            _marker: std::marker::PhantomData::<E>,
        }
    }

    // adapt CosetCombinerGadget for the next domain
    pub fn next_domain(&mut self) {
        self.domain_size >>= self.collapsing_factor;
        self.log_domain_size -= 1;
        self.omega_inv.double();

        assert!(self.log_domain_size > 0);
    }

    fn bitreverse(n: usize, l: usize) -> usize {
        let mut r = n.reverse_bits();
        // now we need to only use the bits that originally were "last" l, so shift
        r >>= (std::mem::size_of::<usize>() * 8) - l;

        r
    }

    pub fn get_coset_idx_for_natural_index<'a>(&self, natural_index: &'a [Boolean]) -> &'a[Boolean] {
        &natural_index[0..(self.log_domain_size - self.collapsing_factor)]
    }
    
    // return the tree index of the current element (when coset combined)
    // also returns  the position of current element inside coset
    pub fn get_coset_idx_for_natural_index_extended<'a>(
        &self,
        natural_index: &'a [Boolean], 
    ) -> (impl Iterator<Item = &'a Boolean>, impl Iterator<Item = &'a Boolean>)
    {    
        // if natural index is of the form yyyy|xxxxxxxx, (here there are collapsing number of y bits)
        // then coset index is equal to xxxxxxxx, and the position of current element in coset is bitreverse(yyyy)
        // hence we return the pair (xxxxxx, bitreverse(yyyyy))

        let a = natural_index[0..(self.log_domain_size - self.collapsing_factor)].iter();
        let b = natural_index[0..self.collapsing_factor].iter().rev();
        (a, b)
    }

    // construct constraint which connects two adjacent layers of 
    pub fn coset_interpolation_value<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        coset_values: &[Num<E>],
        coset_tree_idx: &[Boolean],
        // contains alpha, alpha^2, alpha^4, ...
        challenges: &[AllocatedNum<E>],
        // may be it is a dirty Hack(
        // contains inversed generator of the layer of coset vauers
        constrainted_omega_inv: &AllocatedNum<E>,
    ) -> Result<AllocatedNum<E>, SynthesisError> {

        let coset_size = self.wrapping_factor;
        let mut this_level_values : Vec<Num<E>> = vec![];
        let mut next_level_values : Vec<Num<E>>;
        
        let mut coset_omega_inv = AllocatedNum::pow(
            cs.namespace(|| "get coset specific omega"), 
            constrainted_omega_inv, 
            coset_tree_idx,
        )?;

        let mut omega_inv = self.omega_inv.clone();
        let mut domain_size = self.domain_size;
        let mut log_domain_size = self.log_domain_size;

        let mut interpolant : Option<AllocatedNum<E>> = None;
        
        for wrapping_step in 0..self.collapsing_factor {

            let inputs = if wrapping_step == 0 {
                &coset_values[..]
            } else {
                &this_level_values[..]
            };

            next_level_values = Vec::with_capacity(coset_size >> wrapping_step + 1);

            for (pair_idx, pair) in inputs.chunks(2).enumerate() 
            {
                // let omega denote the generator of the current layer
                // for each pair (f0, f1) with pair_index i
                // pair_omega = coset_omega_inv * omega_inv^(bitinverse(2*i, log_domain_size))
                // v_even = f0 + f1;
                // v_odd = (f0 - f1) * pair_omega;
                // res = (v_odd * challenge + v_even) * two_inv;
                // the last equation is equal to: 
                // v_odd * challenge = 2 * res - v_even

                let one = E::Fr::one();
                let mut minus_one = one.clone();
                minus_one.negate();

                let f0 = pair[0].clone();
                let f1 = pair[1].clone();

                let coef = match pair_idx {
                    0 => one.clone(),
                    _ => {
                        let idx = Self::bitreverse(2 * pair_idx, log_domain_size);
                        omega_inv.pow([idx as u64])
                    },
                };
           
                let mut v_even : Num<E> = f0.clone();
                v_even.add_assign(&f1);

                let mut v_odd : Num<E> = f0.clone();
                v_odd.sub_assign(&f1);
                v_odd = Num::mul_by_var_with_coeff(
                    cs.namespace(|| "scale by coset omega"),
                    &v_odd, 
                    &coset_omega_inv, 
                    coef
                )?.into();

                // res = (v_odd * challenge + v_even) * two_inv;
                // enforce: v_odd * challenge = 2 * res - v_even
                let res = AllocatedNum::alloc(
                    cs.namespace(|| "FRI round consistency check: allocate next layer"), 
                    || { 
                        match (v_odd.get_value(), v_even.get_value(), challenges[wrapping_step].get_value()) {
                            (Some(mut v_odd), Some(v_even), Some(challenge)) => {
                                v_odd.mul_assign(&challenge);
                                v_odd.add_assign(&v_even);
                                v_odd.add_assign(&self.two_inv);
                                Ok(v_odd)
                            },
                            (_, _, _) => Err(SynthesisError::AssignmentMissing),
                        }
                    })?;

                let mut res_num : Num<E> = res.into();
                res_num.scale(self.two.clone());
                res_num.sub_assign(&v_even);

                Num::enforce(
                    cs.namespace(|| "FRI round consistency check constraint"),
                    &v_odd,
                    &challenges[wrapping_step].clone().into(),
                    &res_num,
                );

                next_level_values.push(res_num);
            }

            if wrapping_step != self.collapsing_factor - 1 {
                omega_inv.square();
                domain_size /= 2;
                log_domain_size <<= 1;
                coset_omega_inv = coset_omega_inv.square(cs.namespace(|| "construct next coset omega"))?;
            
                this_level_values = next_level_values;
            } 
            else {
                interpolant = next_level_values.into_iter().nth(0).map(|x| x.force_simplify().expect("this Num should be simple"));
            }         
        }

        interpolant.ok_or(SynthesisError::Unknown)   
    }

    // fri_helper.get_combiner_eval_points(coset_idx)?;
}





