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
use std::marker::PhantomData;

use crate::circuit::num::*;
use crate::circuit::boolean::*;
use crate::circuit::recursive_redshift::hashes::rescue::*;

use super::*;


pub struct RescueTreeGadgetParams<'a, F: PrimeField, RP: RescueParams<F>> {
    pub num_elems_per_leaf: usize,
    pub rescue_params: &'a RP,
    pub _marker: std::marker::PhantomData<F>,
}


pub struct RescueTreeGadget<'a, E: Engine, RP: RescueParams<E::Fr>, SBOX: RescueSbox<E>> {
    num_elems_per_leaf: usize,
    params: &'a RP,
    sbox: SBOX,
    _marker: std::marker::PhantomData<E>,
}

impl<'a, E: Engine, RP: RescueParams<E::Fr>, SBOX: RescueSbox<E>> RescueTreeGadget<'a, E, RP, SBOX> {

    pub fn new_impl(num_elems_per_leaf: usize, params: &'a RP, sbox: SBOX) -> Self {
        Self {
            num_elems_per_leaf,
            params,
            sbox,
            _marker: std::marker::PhantomData::<E>,
        }
    }

    fn hash_elems_into_leaf<CS>(&self, mut cs: CS, elems: &[Num<E>]) -> Result<Num<E>, SynthesisError> 
    where CS: ConstraintSystem<E> {
        assert_eq!(elems.len(), self.num_elems_per_leaf);
        
        let mut hasher = RescueGadget::<E, RP, SBOX>::new(self.params);
        for elem in elems {
            hasher.absorb(elem.clone(), cs.namespace(|| "hashing into leaf: absorbing"), &self.params)?;
        }

        let output = hasher.squeeze(cs.namespace(|| "hashing into leaf: squeezing"), &self.params)?;
        Ok(output)
    }

    fn hash_node<CS>(&self, mut cs: CS, left: AllocatedNum<E>, right: AllocatedNum<E>) -> Result<AllocatedNum<E>, SynthesisError> 
    where CS : ConstraintSystem<E> {

        let mut hasher = RescueGadget::<E, RP, SBOX>::new(self.params);

        hasher.absorb(left.into(), cs.namespace(|| "hashing inside Merklee tree: absorbing"), &self.params)?;
        hasher.absorb(right.into(), cs.namespace(|| "hashing inside Merklee tree: absorbing"), &self.params)?;

        let mut output = hasher.squeeze(cs.namespace(|| "hashing inside Merklee tree: squeezing"), &self.params)?;

        let otput_var = output.simplify(cs.namespace(|| "simplification"))?; 
        
        Ok(otput_var)
    }

    // checks inclusion of the leaf hash into the root
    fn check_hash_inclusion_with_parsed_path<CS: ConstraintSystem<E>>(
        &self, 
        mut cs: CS,
        height: usize,
        root: &AllocatedNum<E>, 
        leaf_hash : AllocatedNum<E>,
        path: &[Boolean], 
        witness: &[AllocatedNum<E>]
    ) -> Result<Boolean, SynthesisError> {
        if height != witness.len() {
            return Err(SynthesisError::Unsatisfiable);
        }

        let mut cur = leaf_hash;

        // Ascend the merkle tree authentication path
        for (i, direction_bit) in path.into_iter()
                                        .enumerate() {
            let cs = &mut cs.namespace(|| format!("merkle tree hash {}", i));

            // "direction_bit" determines if the current subtree
            // is the "right" leaf at this depth of the tree.

            // Witness the authentication path element adjacent
            // at this depth.
            let path_element = &witness[i];

            // Swap the two if the current subtree is on the right
            let (xl, xr) = AllocatedNum::conditionally_reverse(
                cs.namespace(|| "conditional reversal of preimage"),
                &cur,
                path_element,
                &direction_bit
            )?;

            cur = self.hash_node(
                cs.namespace(|| "node hash computation"), 
                xl,
                xr
            )?;
        }

        let included = AllocatedNum::equals(
            cs.namespace(|| "compare roots"), 
            &cur, 
            &root
        )?;

        Ok(included)
    }

    pub fn validate_impl<CS: ConstraintSystem<E>>(
        &self, 
        mut cs: CS,
        height: usize, 
        root: &AllocatedNum<E>, 
        elems : &[Num<E>],
        path: &[Boolean], 
        witness: &[AllocatedNum<E>]
    ) -> Result<Boolean, SynthesisError> {

        let mut leaf_hash = self.hash_elems_into_leaf(cs.namespace(|| "encode elems into leaf"), elems)?;
        let leaf_hash_var = leaf_hash.simplify(cs.namespace(|| "simplification"))?;
        let res = self.check_hash_inclusion_with_parsed_path( 
            cs.namespace(|| "merklee proof"),
            height,
            root,
            leaf_hash_var,
            path, 
            witness,
        );

        res
    }
}


impl<'a, E: Engine, RP: RescueParams<E::Fr>, SBOX: RescueSbox<E>> OracleGadget<E> for RescueTreeGadget<'a, E, RP, SBOX> {
    
    type Params = RescueTreeGadgetParams<'a, E::Fr, RP>;
    type Commitment = AllocatedNum<E>;
    type Proof = Vec<AllocatedNum<E>>;
    

    fn new(params: &Self::Params) -> Self {
        Self::new_impl(params.num_elems_per_leaf, params.rescue_params, SBOX::new())
    }

    fn validate<CS: ConstraintSystem<E>>(
        &self, 
        cs: CS,
        height: usize, 
        elems : &[Num<E>],
        path: &[Boolean],
        commitment: &Self::Commitment, 
        proof: &Self::Proof,
    ) -> Result<Boolean, SynthesisError> {

        self.validate_impl(
            cs,
            height, 
            commitment, 
            elems,
            path,
            proof,
        )
    } 
}


#[cfg(test)]
mod test {
    use bellman::pairing::bn256::{Bn256, Fr};
    use bellman::pairing::ff::{PrimeField, PrimeFieldRepr};
    use bellman::Circuit;
    use bellman::redshift::IOP::hashes::rescue::{Rescue, RescueParams};
    use bellman::redshift::IOP::hashes::rescue::bn256_rescue_params::BN256Rescue;
    
    use bellman::redshift::IOP::oracle::Oracle;
    use bellman::redshift::IOP::oracle::coset_combining_rescue_tree::*;
    
    use crate::circuit::num::AllocatedNum;
    use crate::circuit::boolean::AllocatedBit;    
    use crate::circuit::test::TestConstraintSystem;

    use crate::circuit::recursive_redshift::hashes::rescue::*;
    use crate::circuit::recursive_redshift::hashes::bn256_rescue_sbox::BN256RescueSbox;

    use std::iter::FromIterator;
    use super::*;

    pub fn log2_floor(num: usize) -> usize {
        assert!(num > 0);
        assert!((num & (num - 1)) == 0);

        let mut pow: usize = 0;

        while (1 << (pow+1)) <= num {
            pow += 1;
        }
        pow
    }

    #[test]
    fn test_rescue_merkle_proof_gadget() {
        struct TestCircuit<E: Engine, RP: RescueParams<E::Fr>, SBOX: RescueSbox<E>> {
            size: usize,
            num_elems_per_leaf: usize,
            sbox: SBOX,
            rescue_params: RP,

            root_hash: E::Fr,
            leaf_elems: Vec<E::Fr>,
            index: u64,
            merkle_proof: Vec<E::Fr>,
        }

        impl<E: Engine, RP: RescueParams<E::Fr>, SBOX: RescueSbox<E>> Circuit<E> for TestCircuit<E, RP, SBOX> {
            fn synthesize<CS: ConstraintSystem<E>>(
                self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {

                let root = AllocatedNum::alloc(cs.namespace(|| "allocate root"), || Ok(self.root_hash))?;
                let index = self.index;

                let elems : Vec<Num<E>> = self.leaf_elems.into_iter().map(|e| {
                    let temp = AllocatedNum::alloc(cs.namespace(|| "allocate leaf elem"), || Ok(e)).expect("must allocate");
                    let res : Num<E> = temp.into();
                    res
                }).collect();

                let proof : Vec<AllocatedNum<E>> = self.merkle_proof.into_iter().map(|e| {
                    AllocatedNum::alloc(cs.namespace(|| "allocate merkle proof elem"), || Ok(e)).expect("must allocate")
                }).collect();

                let index = AllocatedNum::alloc(
                    cs.namespace(|| "index"), 
                    || {
                        let mut r = <E::Fr as PrimeField>::Repr::default();
                        r.as_mut()[0] = index;
                        let x = <E::Fr as PrimeField>::from_repr(r).expect("must convert");
                        Ok(x)
                    },
                )?;
                let path = index.into_bits_le(cs.namespace(|| "parse index"))?;

                let tree_params = RescueTreeGadgetParams {
                    num_elems_per_leaf: self.num_elems_per_leaf,
                    rescue_params: &self.rescue_params,
                    _marker: std::marker::PhantomData::<E::Fr>,
                };
                let tree = RescueTreeGadget::<E, RP, SBOX>::new(&tree_params);

                let is_valid = tree.validate(
                    cs.namespace(|| "test merkle proof"),
                    log2_floor(self.size), 
                    &elems[..], 
                    &path,
                    &root, 
                    &proof,
                )?;

                Boolean::enforce_equal(
                    cs.namespace(|| "Validate output bit of Merkle proof"),
                    &is_valid,
                    &Boolean::constant(true),
                )
            }
        }

        let bn256_rescue_params = BN256Rescue::default();

        let (index, root, elems, proof) = {

            let oracle_params = RescueTreeParams {
                values_per_leaf: 4,
                rescue_params: &bn256_rescue_params,
                _marker: std::marker::PhantomData::<Fr>,
            };

            // we are going to create tree constaining 4096 elements, with 4 elements per leaf
            // hence there are 1024 leaves

            let values : Vec<Fr> = (0..4096).scan(Fr::multiplicative_generator(), |cur, _| {
                let res = cur.clone();
                cur.double();
                Some(res)
            }).collect();

            let tree = FriSpecificRescueTree::create(&values[..], &oracle_params);

            assert_eq!(tree.size(), 1024);

            let root = tree.get_commitment();

            // let out index be 42

            let leaf_elements = Vec::from_iter(values[42*4..43*4].iter().cloned());
            let query : CosetCombinedQuery<Fr> = tree.produce_query(42*4..43*4, &values[42*4..43*4], &oracle_params);
            let proof = query.raw_merkle_proof();

            (42, root, leaf_elements, proof)
        };

        let test_circuit = TestCircuit::<Bn256, BN256Rescue, BN256RescueSbox> {
            size: 1024,
            num_elems_per_leaf: 4,
            sbox: BN256RescueSbox{},
            rescue_params: bn256_rescue_params,

            root_hash: root,
            leaf_elems: elems,
            index: index as u64,
            merkle_proof: proof,
        };

        let mut cs = TestConstraintSystem::<Bn256>::new();
        test_circuit.synthesize(&mut cs).expect("should synthesize");

        assert!(cs.is_satisfied());

        println!("Rescue tree for 4096 elements with 4 elements per leaf requires {} constraints", cs.num_constraints());
    }
}