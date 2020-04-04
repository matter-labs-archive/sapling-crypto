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
    omega: E::Fr,
    omega_inv: E::Fr,
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
            omega,
            omega_inv,
            two_inv,
            _marker: std::marker::PhantomData::<E>,
        }
    }

    // adapt CosetCombinerGadget for the next domain
    pub fn next_domain(&mut self) {
        self.domain_size >>= self.collapsing_factor;
        self.log_domain_size -= 1;
        self.omega.double();
        self.omega_inv.double();

        assert!(self.log_domain_size > 0);
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
        cs: mut CS,
        coset_values: &[Num<E>],
        coset_tree_idx: &[Boolean],
        supposed_value: &Num<E>,
        challenge: &AllocatedNum<E>,
        // may be it is a dirty Hack(
        // this array contains generators of all intermediate layers between the layer of coset vauers
        // and the layer of supposed value
        constrainted_generator: &[AllocatedNum<E>],
    ) -> Result<Boolean, SynthesisError> {

        let coset_size = self.wrapping_factor;
        let mut this_level_values = Vec::with_capacity(coset_size/2);
        let mut next_level_values = vec![F::zero(); coset_size / 2];
        
        let mut coset_omega = AllocatedNum::pow(
            cs.namespace(|| "get coset specific omega"), 
            constrainted_generator, 
            coset_tree_idx,
        )?;

        let mut omega = self.omega.clone();
        let mut omega_inv = self.omega_inv.clone();
        let mut domain_size = self.domain_size;
        let mut log_domain_size = self.log_domain_size;
        let mut 
        
        for wrapping_step in 0..collapsing_factor {

            let inputs = if wrapping_step == 0 {
                values
            } else {
                &this_level_values[..(coset_size >> wrapping_step)]
            };

            for (pair_idx, (pair, o)) in inputs.chunks(2).zip(next_level_values.iter_mut()).enumerate() 
            {
                // let omega denote the generator of the current layer
                // for each pair (f0, f1) with pair_index i
                // pair_omega = coset_omega * omega^(bitinverse(2*i, log_domain_size))
                // v_even = f0 + f1

                let idx = bitreverse(base_omega_idx + 2 * pair_idx, *log_domain_size);
                let divisor = omega_inv.pow([idx as u64]);
                let f_at_omega = pair[0];
                let f_at_minus_omega = pair[1];
                let mut v_even_coeffs = f_at_omega;
                v_even_coeffs.add_assign(&f_at_minus_omega);

                let mut v_odd_coeffs = f_at_omega;
                v_odd_coeffs.sub_assign(&f_at_minus_omega);
                v_odd_coeffs.mul_assign(&divisor);

                let mut tmp = v_odd_coeffs;
                tmp.mul_assign(&challenge);
                tmp.add_assign(&v_even_coeffs);
                tmp.mul_assign(&two_inv);

                *o = tmp;
            }

            if wrapping_step != collapsing_factor - 1 {
                this_level_values.clear();
                this_level_values.clone_from(&next_level_values);
                challenge.double();
            }
            
            omega_inv.square();
            *domain_size /= 2;
            *log_domain_size <<= 1;
            *elem_index = (*elem_index << collapsing_factor) % *domain_size;
        }

    next_level_values[0]
    }
    }
}





