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

use std::iter;


pub struct FriUtilsGadget<E: Engine> {
    // these parameters are changed when passing to next domain
    domain_size: usize,
    log_domain_size: usize,
    omega: E::Fr,
    omega_inv: E::Fr,
    layer: usize,
    first_pass: bool,
    // these parameters are constant for current UtilsGadget
    collapsing_factor: usize,
    wrapping_factor: usize,
    initial_domain_size: usize,
    initial_log_domain_size: usize,
    initial_omega: E::Fr,
    initial_omega_inv: E::Fr,
    num_iters: usize,
    two: E::Fr,
    two_inv: E::Fr,
    // remaining data is filled in on the first passing through all layers
    // it is reused on next acess to the same arrays

    // may be it is a dirty Hack(
    // contains inversed generators of the layers
    constrainted_omega_inv_arr: Vec<AllocatedNum<E>>,
    constrainted_top_level_omega: Option<AllocatedNum<E>>,
    constrainted_bottom_level_omega: Option<AllocatedNum<E>>,

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

    pub fn get_topmost_layer_omega<CS>(&mut self, mut cs: CS) -> Result<&AllocatedNum<E>, SynthesisError>
    where CS: ConstraintSystem<E> 
    {
        if self.layer != 0 {
            return Err(SynthesisError::Unknown);
        }

        let val = self.omega.clone();
        let res = self.constrainted_top_level_omega.get_or_insert_with(|| {
            AllocatedNum::alloc(
                cs.namespace(|| "constrainted top-level omega"), 
                || {Ok(val)}
            ).expect("should create")
        });

        Ok(res)   
    }

    pub fn get_bottom_layer_omega<CS>(&mut self, mut cs: CS) -> Result<&AllocatedNum<E>, SynthesisError>
    where CS: ConstraintSystem<E> 
    {
        if self.layer != self.num_iters - 1 {
            return Err(SynthesisError::Unknown);
        }

        let val = self.omega.clone();
        let res = self.constrainted_bottom_level_omega.get_or_insert_with(|| {
            AllocatedNum::alloc(
                cs.namespace(|| "constrainted top-level omega"), 
                || {Ok(val)}
            ).expect("should create")
        });

        Ok(res)  
    }

    pub fn get_cur_layer_omega_inv(&self) -> &AllocatedNum<E> {
        &self.constrainted_omega_inv_arr[self.layer]
    }

    //wrapping factor here is size of coset: 1 << collapsing_factor
    pub fn new<CS: ConstraintSystem<E>>(mut cs: CS, domain_size: usize, collapsing_factor: usize, num_iters: usize) -> Self {
        
        assert!(domain_size.is_power_of_two());
        let log_domain_size = Self::log2_floor(domain_size);

        let domain = Domain::<E::Fr>::new_for_size(domain_size as u64).expect("should construct");
        let omega = domain.generator;
        let omega_inv = omega.inverse().expect("should exist");

        let mut two = E::Fr::one();
        two.double();
        let two_inv = two.inverse().expect("should exist");

        let mut constrainted_omega_inv_arr = Vec::with_capacity(num_iters);
        let constrainted_omega_inv = AllocatedNum::alloc(
            cs.namespace(|| "generator (inv) of domain constrainted"), 
            || {Ok(omega_inv.clone())}
        ).expect("should create");
        constrainted_omega_inv_arr.push(constrainted_omega_inv);

        FriUtilsGadget {
            
            first_pass: true,
            domain_size,
            log_domain_size,
            omega : omega.clone(),
            omega_inv : omega_inv.clone(),
            layer: 0,
    
            collapsing_factor,
            wrapping_factor: 1 << collapsing_factor,
            initial_domain_size: domain_size,
            initial_log_domain_size: log_domain_size,
            initial_omega : omega,
            initial_omega_inv: omega_inv,
            num_iters,
            two,
            two_inv,

            constrainted_omega_inv_arr,
            constrainted_top_level_omega: None,
            constrainted_bottom_level_omega: None,

            _marker: std::marker::PhantomData::<E>,
        }
    }

    // adapt CosetCombinerGadget for the next domain
    pub fn next_domain<CS: ConstraintSystem<E>>(&mut self, mut cs: CS) {

        self.domain_size >>= self.collapsing_factor;
        self.log_domain_size -= 1;
        self.omega.square();
        self.omega_inv.square();
        self.layer += 1;
        assert!(self.layer < self.num_iters);
        assert!(self.log_domain_size > 0);

        if self.first_pass {
            let constrainted_omega_inv = self.constrainted_omega_inv_arr[self.layer-1].square(
                cs.namespace(|| "generator (inv) of domain constrainted")
            ).expect("should create");
            self.constrainted_omega_inv_arr.push(constrainted_omega_inv);
        }
       
    }

    pub fn to_initial_domain(&mut self) {
        
        self.domain_size = self.initial_domain_size;
        self.log_domain_size = self.initial_log_domain_size;
        self.omega = self.initial_omega.clone();
        self.omega_inv = self.initial_omega_inv.clone();
        self.layer = 0;
        self.first_pass = false;
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

    pub fn get_coset_offset_for_natural_index<'a>(
        &self, 
        natural_index: &'a [Boolean]
    ) -> impl DoubleEndedIterator<Item = &'a Boolean> 
    {
        natural_index[self.log_domain_size - self.collapsing_factor..].iter().rev()
    }
    
    // return the tree index of the current element (when coset combined)
    // also returns  the position of current element inside coset
    pub fn get_coset_idx_for_natural_index_extended<'a>(
        &self,
        natural_index: &'a [Boolean], 
    ) -> (impl DoubleEndedIterator<Item = &'a Boolean>, impl DoubleEndedIterator<Item = &'a Boolean>)
    {    
        // if natural index is of the form yyyy|xxxxxxxx, (here there are collapsing number of y bits)
        // then coset index is equal to xxxxxxxx, and the position of current element in coset is bitreverse(yyyy)
        // hence we return the pair (xxxxxx, bitreverse(yyyyy))

        let (a, b) = natural_index.split_at(self.log_domain_size - self.collapsing_factor);
        (a.iter(), b.iter().rev())
    }

    // this method solver the following task: 
    // we are given elements of coset: (a_0, a_1, ..., a_n) and coset_index i \in [0, n]
    // we want to take particular element according to the index
    pub fn choose_element_in_coset<'a, CS, I>(&self, mut cs: CS, coset: &mut [Num<E>], index: I) -> Result<AllocatedNum<E>, SynthesisError>
    where CS: ConstraintSystem<E>, I : Iterator<Item = &'a Boolean>,
    {

        assert_eq!(coset.len(), self.wrapping_factor);
        let mut array : Vec<AllocatedNum<E>> = Vec::with_capacity(3 * self.wrapping_factor /2 );
        // first, simplify all Nums
        for (elem, o) in coset.iter_mut().zip(array.iter_mut()) {
            *o = elem.simplify(cs.namespace(|| "simplification"))?;
        }
        array.extend(iter::repeat(AllocatedNum::default::<CS>()).take(self.wrapping_factor / 2));    

        for (elem, o) in coset.iter_mut().zip(array[..self.wrapping_factor].iter_mut()) {
            *o = elem.simplify(cs.namespace(|| "simplification"))?;
        }

        let mut take_left_part = true;
        let mut input_len = self.wrapping_factor;

        for (i, bit) in index.enumerate() {
            
            let (left_part, right_part) = array.split_at_mut(self.wrapping_factor);
            let (input, output) = match take_left_part {
                true => (&left_part[0..input_len], &mut right_part[0..input_len/2]),
                false => (&right_part[0..input_len], &mut left_part[0..input_len/2]), 
            };

            for (pair, o) in input.chunks(2).zip(output.iter_mut()) {
                *o = AllocatedNum::conditionally_select(
                    cs.namespace(|| "chooser"), 
                    &pair[1], 
                    &pair[0],
                    bit,
                )?;
            }

            take_left_part = !take_left_part;
            input_len >>= 1;
        }
        
        let res = match take_left_part {
            true => array.into_iter().nth(0),
            false => array.into_iter().nth(self.wrapping_factor),
        };

        res.ok_or(SynthesisError::Unknown)
    }

    // construct constraint which connects two adjacent layers of 
    pub fn coset_interpolation_value<'a, CS: ConstraintSystem<E>, I: DoubleEndedIterator<Item = &'a Boolean>>(
        &self,
        mut cs: CS,
        coset_values: &[Num<E>],
        coset_tree_idx: I,
        // contains alpha, alpha^2, alpha^4, ...
        challenges: &[AllocatedNum<E>],
    ) -> Result<AllocatedNum<E>, SynthesisError> {

        let coset_size = self.wrapping_factor;
        let mut this_level_values : Vec<Num<E>> = vec![];
        let mut next_level_values : Vec<Num<E>>;
        
        let mut coset_omega_inv = AllocatedNum::pow(
            cs.namespace(|| "get coset specific omega"),
            self.get_cur_layer_omega_inv(),
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

    pub fn get_combiner_eval_points<'a, CS, I>(&self, mut cs: CS, coset_tree_idx : I) -> Result<Vec<Num<E>>, SynthesisError>
    where CS: ConstraintSystem<E>, I: DoubleEndedIterator<Item = &'a Boolean> {

        // let w - generator of current domain
        // let coset_idx = |xxxxxx| (bit decomposition)
        // let coset_omega = w^coset_idx
        // let g = w^(1000000)
        // this method returns array [coset_omega * g^bitreverse(i)]

        // Note: we don't constraint omegas by default (only omegas inverse)

        let constrainted_omega = AllocatedNum::alloc(
            cs.namespace(|| "generator of domain constrainted"), 
            || {Ok(self.omega.clone())}
        ).expect("should create");

        let coset_omega = AllocatedNum::pow(
            cs.namespace(|| "get coset specific omega"), 
            &constrainted_omega, 
            coset_tree_idx,
        )?;
        
        let shift = self.log_domain_size - self.collapsing_factor;
        let g = self.omega.pow([1 << shift as u64]);

        let mut res : Vec<Num<E>> = Vec::with_capacity(self.wrapping_factor);

        for i in 0..self.wrapping_factor {

            let coef = g.pow([Self::bitreverse(i, self.wrapping_factor) as u64]);
            let mut num : Num<E> = coset_omega.clone().into();
            num.scale(coef); 
            res.push(num);
        }

        Ok(res)       
    }
}





