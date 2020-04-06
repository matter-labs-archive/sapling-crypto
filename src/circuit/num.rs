use bellman::pairing::{
    Engine,
};

use bellman::pairing::ff::{
    Field,
    PrimeField,
    PrimeFieldRepr,
    BitIterator
};

use bellman::{
    SynthesisError,
    ConstraintSystem,
    LinearCombination,
    Variable
};

use super::{
    Assignment
};

use super::boolean::{
    self,
    Boolean,
    AllocatedBit
};

pub struct AllocatedNum<E: Engine> {
    value: Option<E::Fr>,
    variable: Variable
}

impl<E: Engine> Clone for AllocatedNum<E> {
    fn clone(&self) -> Self {
        AllocatedNum {
            value: self.value,
            variable: self.variable
        }
    }
}

impl<E: Engine> AllocatedNum<E> {
    pub fn default<CS: ConstraintSystem<E>>() -> Self {
        AllocatedNum {
            value: Some(E::Fr::one()),
            variable: CS::one()
        }
    }

    pub fn alloc<CS, F>(
        mut cs: CS,
        value: F,
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>,
              F: FnOnce() -> Result<E::Fr, SynthesisError>
    {
        let mut new_value = None;
        let var = cs.alloc(|| "num", || {
            let tmp = value()?;

            new_value = Some(tmp);

            Ok(tmp)
        })?;

        Ok(AllocatedNum {
            value: new_value,
            variable: var
        })
    }

    pub fn alloc_input<CS, F>(
        mut cs: CS,
        value: F,
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>,
              F: FnOnce() -> Result<E::Fr, SynthesisError>
    {
        let mut new_value = None;
        let var = cs.alloc_input(|| "num", || {
            let tmp = value()?;

            new_value = Some(tmp);

            Ok(tmp)
        })?;

        Ok(AllocatedNum {
            value: new_value,
            variable: var
        })
    }

    pub fn from_var(variable: Variable, value: Option<E::Fr>) -> Self {
        AllocatedNum {
            value,
            variable,
        }
    } 

    pub fn inputize<CS>(
        &self,
        mut cs: CS
    ) -> Result<(), SynthesisError>
        where CS: ConstraintSystem<E>
    {
        let input = cs.alloc_input(
            || "input variable",
            || {
                Ok(*self.value.get()?)
            }
        )?;

        cs.enforce(
            || "enforce input is correct",
            |lc| lc + input,
            |lc| lc + CS::one(),
            |lc| lc + self.variable
        );

        Ok(())
    }

    /// Deconstructs this allocated number into its
    /// boolean representation in little-endian bit
    /// order, requiring that the representation
    /// strictly exists "in the field" (i.e., a
    /// congruency is not allowed.)
    pub fn into_bits_le_strict<CS>(
        &self,
        mut cs: CS
    ) -> Result<Vec<Boolean>, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        pub fn kary_and<E, CS>(
            mut cs: CS,
            v: &[AllocatedBit]
        ) -> Result<AllocatedBit, SynthesisError>
            where E: Engine,
                  CS: ConstraintSystem<E>
        {
            assert!(v.len() > 0);

            // Let's keep this simple for now and just AND them all
            // manually
            let mut cur = None;

            for (i, v) in v.iter().enumerate() {
                if cur.is_none() {
                    cur = Some(v.clone());
                } else {
                    cur = Some(AllocatedBit::and(
                        cs.namespace(|| format!("and {}", i)),
                        cur.as_ref().unwrap(),
                        v
                    )?);
                }
            }

            Ok(cur.expect("v.len() > 0"))
        }

        // We want to ensure that the bit representation of a is
        // less than or equal to r - 1.
        let mut a = self.value.map(|e| BitIterator::new(e.into_repr()));
        let mut b = E::Fr::char();
        b.sub_noborrow(&1.into());

        let mut result = vec![];

        // Runs of ones in r
        let mut last_run = None;
        let mut current_run = vec![];

        let mut found_one = false;
        let mut i = 0;
        for b in BitIterator::new(b) {
            let a_bit = a.as_mut().map(|e| e.next().unwrap());

            // Skip over unset bits at the beginning
            found_one |= b;
            if !found_one {
                // a_bit should also be false
                a_bit.map(|e| assert!(!e));
                continue;
            }

            if b {
                // This is part of a run of ones. Let's just
                // allocate the boolean with the expected value.
                let a_bit = AllocatedBit::alloc(
                    cs.namespace(|| format!("bit {}", i)),
                    a_bit
                )?;
                // ... and add it to the current run of ones.
                current_run.push(a_bit.clone());
                result.push(a_bit);
            } else {
                if current_run.len() > 0 {
                    // This is the start of a run of zeros, but we need
                    // to k-ary AND against `last_run` first.

                    if last_run.is_some() {
                        current_run.push(last_run.clone().unwrap());
                    }
                    last_run = Some(kary_and(
                        cs.namespace(|| format!("run ending at {}", i)),
                        &current_run
                    )?);
                    current_run.truncate(0);
                }

                // If `last_run` is true, `a` must be false, or it would
                // not be in the field.
                //
                // If `last_run` is false, `a` can be true or false.

                let a_bit = AllocatedBit::alloc_conditionally(
                    cs.namespace(|| format!("bit {}", i)),
                    a_bit,
                    &last_run.as_ref().expect("char always starts with a one")
                )?;
                result.push(a_bit);
            }

            i += 1;
        }

        // char is prime, so we'll always end on
        // a run of zeros.
        assert_eq!(current_run.len(), 0);

        // Now, we have `result` in big-endian order.
        // However, now we have to unpack self!

        let mut lc = LinearCombination::zero();
        let mut coeff = E::Fr::one();

        for bit in result.iter().rev() {
            lc = lc + (coeff, bit.get_variable());

            coeff.double();
        }

        lc = lc - self.variable;

        cs.enforce(
            || "unpacking constraint",
            |lc| lc,
            |lc| lc,
            |_| lc
        );

        // Convert into booleans, and reverse for little-endian bit order
        Ok(result.into_iter().map(|b| Boolean::from(b)).rev().collect())
    }

    /// Convert the allocated number into its little-endian representation.
    /// Note that this does not strongly enforce that the commitment is
    /// "in the field."
    pub fn into_bits_le<CS>(
        &self,
        mut cs: CS
    ) -> Result<Vec<Boolean>, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        let bits = boolean::field_into_allocated_bits_le(
            &mut cs,
            self.value
        )?;

        let mut lc = LinearCombination::zero();
        let mut coeff = E::Fr::one();

        for bit in bits.iter() {
            lc = lc + (coeff, bit.get_variable());

            coeff.double();
        }

        lc = lc - self.variable;

        cs.enforce(
            || "unpacking constraint",
            |lc| lc,
            |lc| lc,
            |_| lc
        );

        Ok(bits.into_iter().map(|b| Boolean::from(b)).collect())
    }

    pub fn mul<CS>(
        &self,
        mut cs: CS,
        other: &Self
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        let mut value = None;

        let var = cs.alloc(|| "product num", || {
            let mut tmp = *self.value.get()?;
            tmp.mul_assign(other.value.get()?);

            value = Some(tmp);

            Ok(tmp)
        })?;

        // Constrain: a * b = ab
        cs.enforce(
            || "multiplication constraint",
            |lc| lc + self.variable,
            |lc| lc + other.variable,
            |lc| lc + var
        );

        Ok(AllocatedNum {
            value: value,
            variable: var
        })
    }

    pub fn square<CS>(
        &self,
        mut cs: CS
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        let mut value = None;

        let var = cs.alloc(|| "squared num", || {
            let mut tmp = *self.value.get()?;
            tmp.square();

            value = Some(tmp);

            Ok(tmp)
        })?;

        // Constrain: a * a = aa
        cs.enforce(
            || "squaring constraint",
            |lc| lc + self.variable,
            |lc| lc + self.variable,
            |lc| lc + var
        );

        Ok(AllocatedNum {
            value: value,
            variable: var
        })
    }

    pub fn assert_nonzero<CS>(
        &self,
        mut cs: CS
    ) -> Result<(), SynthesisError>
        where CS: ConstraintSystem<E>
    {
        let inv = cs.alloc(|| "ephemeral inverse", || {
            let tmp = *self.value.get()?;
            
            if tmp.is_zero() {
                Err(SynthesisError::DivisionByZero)
            } else {
                Ok(tmp.inverse().unwrap())
            }
        })?;

        // Constrain a * inv = 1, which is only valid
        // iff a has a multiplicative inverse, untrue
        // for zero.
        cs.enforce(
            || "nonzero assertion constraint",
            |lc| lc + self.variable,
            |lc| lc + inv,
            |lc| lc + CS::one()
        );

        Ok(())
    }

    pub fn assert_zero<CS>(
        &self,
        mut cs: CS
    ) -> Result<(), SynthesisError>
        where CS: ConstraintSystem<E>
    {
        cs.enforce(
            || "zero assertion constraint",
            |lc| lc + self.variable,
            |lc| lc + CS::one(),
            |lc| lc
        );

        Ok(())
    }

    /// Takes two allocated numbers (a, b) and returns
    /// (b, a) if the condition is true, and (a, b)
    /// otherwise.
    pub fn conditionally_reverse<CS>(
        mut cs: CS,
        a: &Self,
        b: &Self,
        condition: &Boolean
    ) -> Result<(Self, Self), SynthesisError>
        where CS: ConstraintSystem<E>
    {
        let c = Self::alloc(
            cs.namespace(|| "conditional reversal result 1"),
            || {
                if *condition.get_value().get()? {
                    Ok(*b.value.get()?)
                } else {
                    Ok(*a.value.get()?)
                }
            }
        )?;

        cs.enforce(
            || "first conditional reversal",
            |lc| lc + a.variable - b.variable,
            |_| condition.lc(CS::one(), E::Fr::one()),
            |lc| lc + a.variable - c.variable
        );

        let d = Self::alloc(
            cs.namespace(|| "conditional reversal result 2"),
            || {
                if *condition.get_value().get()? {
                    Ok(*a.value.get()?)
                } else {
                    Ok(*b.value.get()?)
                }
            }
        )?;

        cs.enforce(
            || "second conditional reversal",
            |lc| lc + b.variable - a.variable,
            |_| condition.lc(CS::one(), E::Fr::one()),
            |lc| lc + b.variable - d.variable
        );

        Ok((c, d))
    }

    /// Takes two allocated numbers (a, b) and returns
    /// a if the condition is true, and b
    /// otherwise.
    /// Most often to be used with b = 0
    pub fn conditionally_select<CS>(
        mut cs: CS,
        a: &Self,
        b: &Self,
        condition: &Boolean
    ) -> Result<(Self), SynthesisError>
        where CS: ConstraintSystem<E>
    {
        let c = Self::alloc(
            cs.namespace(|| "conditional select result"),
            || {
                if *condition.get_value().get()? {
                    Ok(*a.value.get()?)
                } else {
                    Ok(*b.value.get()?)
                }
            }
        )?;

        // a * condition + b*(1-condition) = c ->
        // a * condition - b*condition = c - b

        cs.enforce(
            || "conditional select constraint",
            |lc| lc + a.variable - b.variable,
            |_| condition.lc(CS::one(), E::Fr::one()),
            |lc| lc + c.variable - b.variable
        );

        Ok(c)
    }

    /// Limits number of bits. The easiest example when required
    /// is to add or subtract two "small" (with bit length smaller 
    /// than one of the field) numbers and check for overflow
    /// return the bit packed result
    pub fn convert_to_bits<CS>(
        &self,
        mut cs: CS,
        number_of_bits: usize
    ) -> Result<Vec<Boolean>, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        // do the bit decomposition and check that higher bits are all zeros

        let mut bits = self.into_bits_le(
            cs.namespace(|| "unpack to limit number of bits")
        )?;

        let lower_bits : Vec<Boolean> = bits.drain(0..number_of_bits).into_iter().map(|b| Boolean::from(b)).collect();

        // repack

        let mut top_bits_lc = Num::<E>::zero();
        let mut coeff = E::Fr::one();
        for bit in bits.into_iter() {
            top_bits_lc = top_bits_lc.add_bool_with_coeff(CS::one(), &bit, coeff);
            coeff.double();
        }

        // enforce packing and zeroness
        cs.enforce(
            || "repack top bits",
            |lc| lc,
            |lc| lc + CS::one(),
            |_| top_bits_lc.lc(E::Fr::one())
        );

        Ok(lower_bits)
    }

    /// same as previousm but doesn't return anything
    pub fn limit_number_of_bits<CS>(
        &self,
        mut cs: CS,
        number_of_bits: usize
    ) -> Result<(), SynthesisError>
        where CS: ConstraintSystem<E>
    {
        // do the bit decomposition and check that higher bits are all zeros

        let mut bits = self.into_bits_le(
            cs.namespace(|| "unpack to limit number of bits")
        )?;

        bits.drain(0..number_of_bits);

        // repack

        let mut top_bits_lc = Num::<E>::zero();
        let mut coeff = E::Fr::one();
        for bit in bits.into_iter() {
            top_bits_lc = top_bits_lc.add_bool_with_coeff(CS::one(), &bit, coeff);
            coeff.double();
        }

        // enforce packing and zeroness
        cs.enforce(
            || "repack top bits",
            |lc| lc,
            |lc| lc + CS::one(),
            |_| top_bits_lc.lc(E::Fr::one())
        );

        Ok(())
    }

    /// Takes two allocated numbers (a, b) and returns
    /// allocated boolean variable with value `true`
    /// if the `a` and `b` are equal, `false` otherwise.
    pub fn equals<CS>(
        mut cs: CS,
        a: &Self,
        b: &Self
    ) -> Result<boolean::Boolean, SynthesisError>
        where E: Engine,
            CS: ConstraintSystem<E>
    {
        // Allocate and constrain `r`: result boolean bit. 
        // It equals `true` if `a` equals `b`, `false` otherwise

        let r_value = match (a.get_value(), b.get_value()) {
            (Some(a), Some(b))  => Some(a == b),
            _                   => None,
        };

        let r = boolean::AllocatedBit::alloc(
            cs.namespace(|| "r"), 
            r_value
        )?;

        let delta = Self::alloc(
            cs.namespace(|| "delta"), 
            || {
                let a_value = *a.get_value().get()?;
                let b_value = *b.get_value().get()?;

                let mut delta = a_value;
                delta.sub_assign(&b_value);

                Ok(delta)
            }
        )?;

        // 
        cs.enforce(
            || "delta = (a - b)",
            |lc| lc + a.get_variable() - b.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + delta.get_variable(),
        );

        let delta_inv = Self::alloc(
            cs.namespace(|| "delta_inv"), 
            || {
                let delta = *delta.get_value().get()?;

                if delta.is_zero() {
                    Ok(E::Fr::one()) // we can return any number here, it doesn't matter
                } else {
                    Ok(delta.inverse().unwrap())
                }
            }
        )?;

        // Allocate `t = delta * delta_inv`
        // If `delta` is non-zero (a != b), `t` will equal 1
        // If `delta` is zero (a == b), `t` cannot equal 1

        let t = Self::alloc(
            cs.namespace(|| "t"),
            || {
                let mut tmp = *delta.get_value().get()?;
                tmp.mul_assign(&(*delta_inv.get_value().get()?));

                Ok(tmp)
            }
        
        )?;

        // Constrain allocation: 
        // t = (a - b) * delta_inv
        cs.enforce(
            || "t = (a - b) * delta_inv",
            |lc| lc + a.get_variable() - b.get_variable(),
            |lc| lc + delta_inv.get_variable(),
            |lc| lc + t.get_variable(),
        );

        // Constrain: 
        // (a - b) * (t - 1) == 0
        // This enforces that correct `delta_inv` was provided, 
        // and thus `t` is 1 if `(a - b)` is non zero (a != b )
        cs.enforce(
            || "(a - b) * (t - 1) == 0",
            |lc| lc + a.get_variable() - b.get_variable(),
            |lc| lc + t.get_variable() - CS::one(),
            |lc| lc
        );

        // Constrain: 
        // (a - b) * r == 0
        // This enforces that `r` is zero if `(a - b)` is non-zero (a != b)
        cs.enforce(
            || "(a - b) * r == 0",
            |lc| lc + a.get_variable() - b.get_variable(),
            |lc| lc + r.get_variable(),
            |lc| lc
        );

        // Constrain: 
        // (t - 1) * (r - 1) == 0
        // This enforces that `r` is one if `t` is not one (a == b)
        cs.enforce(
            || "(t - 1) * (r - 1) == 0",
            |lc| lc + t.get_variable() - CS::one(),
            |lc| lc + r.get_variable() - CS::one(),
            |lc| lc
        );

        Ok(boolean::Boolean::from(r))
    }

    pub fn get_value(&self) -> Option<E::Fr> {
        self.value
    }

    pub fn get_variable(&self) -> Variable {
        self.variable
    }

    // Montgomery double and add algorithm
    pub fn pow<'a, CS, I>(mut cs: CS, base: &Self, x: I) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>, I: DoubleEndedIterator<Item = &'a Boolean> 
    {
        let mut r0 = Self::from_var(CS::one(), Some(E::Fr::one()));
        let mut r1 = base.clone();
        for b in x.rev() {
            // RO = RO * R1 if b == 1 else R0^2
            // R1 = R1^2 if b == 1 else R0 * R1
            let r0_squared = r0.square(cs.namespace(|| "square R0"))?;
            let r1_squared = r1.square(cs.namespace(|| "square R1"))?;
            let r0_times_r1 = r0.mul(cs.namespace(|| "R0 x R1"), &r1)?;
            
            r0 = AllocatedNum::conditionally_select(
                cs.namespace(|| "construct R0 iteration"),
                &r0_times_r1,
                &r0_squared,
                b,
            )?;

            r1 = AllocatedNum::conditionally_select(
                cs.namespace(|| "construct R1 iteration"),
                &r1_squared,
                &r0_times_r1,
                b,
            )?;
        }

        Ok(r0)
    }
}

pub struct Num<E: Engine> {
    value: Option<E::Fr>,
    lc: LinearCombination<E>
}

impl<E: Engine> From<AllocatedNum<E>> for Num<E> {
    fn from(num: AllocatedNum<E>) -> Num<E> {
        Num {
            value: num.value,
            lc: LinearCombination::<E>::zero() + num.variable
        }
    }
}

impl<E: Engine> Clone for Num<E> {
    fn clone(&self) -> Self {
        Num {
            value: self.value,
            lc: self.lc.clone()
        }
    }
}


impl<E: Engine> Num<E> {
    pub fn zero() -> Self {
        Num {
            value: Some(E::Fr::zero()),
            lc: LinearCombination::zero()
        }
    }

    pub fn from_constant<CS: ConstraintSystem<E>>(c: &E::Fr, cs: &CS) -> Self {
        Num {
            value: Some(c.clone()),
            lc: LinearCombination::zero() + (c.clone(), CS::one())
        }
    }

    pub fn get_value(&self) -> Option<E::Fr> {
        self.value
    }

    pub fn get_lc(&self) -> &LinearCombination<E> {
        &self.lc
    }

    pub fn lc(&self, coeff: E::Fr) -> LinearCombination<E> {
        LinearCombination::zero() + (coeff, &self.lc)
    }

    pub fn scale(&mut self, coeff: E::Fr) {
        let newval = match self.value {
            Some(mut curval) => {
                curval.mul_assign(&coeff);

                Some(curval)
            },
            _ => None
        };

        self.value = newval;
        // TODO: Reword bellman to allow linear combinations to scale in-place
        self.lc = LinearCombination::zero() + (coeff, &self.lc);
    }

    pub fn add_number_with_coeff(
        self,
        variable: &AllocatedNum<E>,
        coeff: E::Fr
    ) -> Self
    {
        let newval = match (self.value, variable.get_value()) {
            (Some(mut curval), Some(val)) => {
                let mut tmp = val;
                tmp.mul_assign(&coeff);

                curval.add_assign(&tmp);

                Some(curval)
            },
            _ => None
        };

        Num {
            value: newval,
            lc: self.lc + (coeff, variable.get_variable())
        }
    }

    pub fn add_bool_with_coeff(
        self,
        one: Variable,
        bit: &Boolean,
        coeff: E::Fr
    ) -> Self
    {
        let newval = match (self.value, bit.get_value()) {
            (Some(mut curval), Some(bval)) => {
                if bval {
                    curval.add_assign(&coeff);
                }

                Some(curval)
            },
            _ => None
        };

        Num {
            value: newval,
            lc: self.lc + &bit.lc(one, coeff)
        }
    }

    pub fn mut_add_number_with_coeff(
        &mut self,
        variable: &AllocatedNum<E>,
        coeff: E::Fr
    )
    {
        let newval = match (self.value, variable.get_value()) {
            (Some(mut curval), Some(val)) => {
                let mut tmp = val;
                tmp.mul_assign(&coeff);

                curval.add_assign(&tmp);

                Some(curval)
            },
            _ => None
        };

        self.value = newval;
        let mut lc = LinearCombination::zero();
        std::mem::swap(&mut self.lc, &mut lc);
        self.lc = lc + (coeff, variable.get_variable());
    }

    pub fn mut_add_bool_with_coeff(
        &mut self,
        one: Variable,
        bit: &Boolean,
        coeff: E::Fr
    )
    {
        let newval = match (self.value, bit.get_value()) {
            (Some(mut curval), Some(bval)) => {
                if bval {
                    curval.add_assign(&coeff);
                }

                Some(curval)
            },
            _ => None
        };

        self.value = newval;
        let mut lc = LinearCombination::zero();
        std::mem::swap(&mut self.lc, &mut lc);
        self.lc = lc + &bit.lc(one, coeff);
    }

    pub fn add_assign(
        &mut self,
        other: &Self
    )
    {
        let newval = match (self.value, other.get_value()) {
            (Some(mut curval), Some(otherval)) => {
                curval.add_assign(&otherval);

                Some(curval)
            },
            _ => None
        };

        self.value = newval;
        let mut lc = LinearCombination::zero();
        // std::mem::swap(&mut self.lc, &mut lc);
        use std::collections::HashMap;
        let mut final_coeffs: HashMap<bellman::Variable, E::Fr> = HashMap::new();
        for (var, coeff) in self.lc.as_ref() {
            if final_coeffs.get(var).is_some() {
                if let Some(existing_coeff) = final_coeffs.get_mut(var) {
                    existing_coeff.add_assign(&coeff);
                } 
            } else {
                final_coeffs.insert(*var, *coeff);
            }
        }

        for (var, coeff) in other.lc.as_ref() {
            if final_coeffs.get(var).is_some() {
                if let Some(existing_coeff) = final_coeffs.get_mut(var) {
                    existing_coeff.add_assign(&coeff);
                }
            } else {
                final_coeffs.insert(*var, *coeff);
            }
        }
        for (var, coeff) in final_coeffs.into_iter() {
            lc = lc + (coeff, var);
        }
        self.lc = lc;
    }

    pub fn sub_assign(
        &mut self,
        other: &Self
    )
    {
        let newval = match (self.value, other.get_value()) {
            (Some(mut curval), Some(otherval)) => {
                curval.sub_assign(&otherval);

                Some(curval)
            },
            _ => None
        };

        self.value = newval;
        let mut lc = LinearCombination::zero();
        // std::mem::swap(&mut self.lc, &mut lc);
        use std::collections::HashMap;
        let mut final_coeffs: HashMap<bellman::Variable, E::Fr> = HashMap::new();
        for (var, coeff) in self.lc.as_ref() {
            if final_coeffs.get(var).is_some() {
                if let Some(existing_coeff) = final_coeffs.get_mut(var) {
                    existing_coeff.add_assign(&coeff);
                } 
            } else {
                final_coeffs.insert(*var, *coeff);
            }
        }

        for (var, coeff) in other.lc.as_ref() {
            if final_coeffs.get(var).is_some() {
                if let Some(existing_coeff) = final_coeffs.get_mut(var) {
                    existing_coeff.sub_assign(&coeff);
                }
            } else {
                final_coeffs.insert(*var, *coeff);
            }
        }
        for (var, coeff) in final_coeffs.into_iter() {
            lc = lc + (coeff, var);
        }
        self.lc = lc;
    }

    /// check is the combination in question exactly contains the only one element (or even empty)
    /// it yes - recombine and return that unique element
    pub fn simplify<CS: ConstraintSystem<E>>(&mut self, mut cs: CS) -> Result<AllocatedNum<E>, SynthesisError> {

        let in_lc = self.get_lc();

        assert!(!in_lc.is_empty(), " lc is empty before simplification");
        
        let res = match in_lc.is_simple() {
            Some(x) => AllocatedNum::from_var(x, self.get_value()),
            None => {
                let out_alloc = AllocatedNum::alloc(
                    cs.namespace(|| "simplified element"),
                    || { self.get_value().ok_or(SynthesisError::AssignmentMissing)} 
                )?;

                cs.enforce(
                    || "simplified element = input element", 
                    |lc| lc + in_lc, 
                    |lc| lc + CS::one(),
                    |lc| lc + out_alloc.get_variable(),
                );
                    
                // As we've constrained this currentcombination, we can
                // substitute for the new variable to shorten subsequent combinations.
                self.lc = LinearCombination::zero() + out_alloc.get_variable();
                
                out_alloc
            }, 
        };

        Ok(res)
    }

    /// Sometimes we apriori know that our Num is simple (contains only one AllocedNum with trivial coefficient).
    /// This method tries to get that AllocatedNum and returns error if we are mistaken in our assumption 
    /// of the forn of Num (i.e. it is not simple)
    pub fn force_simplify(&self) -> Result<AllocatedNum<E>, SynthesisError> {
        self.get_lc().is_simple().map(|x| AllocatedNum::from_var(x, self.get_value())).ok_or(SynthesisError::Unknown)
    }

    /// in R1CS multiplication of two linear combinations will inevitably lead
    /// to the allocation of new variable
    pub fn mul<CS>(mut cs: CS, left: &Self, right: &Self) -> Result<AllocatedNum<E>, SynthesisError>
    where CS: ConstraintSystem<E>
    {
        let res = AllocatedNum::alloc(
            cs.namespace(|| "mul of two Nums"), 
            || {
            match (left.get_value(), right.get_value()) {
                (Some(mut x), Some(y)) => {
                    x.mul_assign(&y);
                    Ok(x)
                }
                (_, _) => Err(SynthesisError::AssignmentMissing)       
            }
        })?;
        
        cs.enforce(
            || "multiplication check",
            |lc| lc + left.get_lc(),
            |lc| lc + right.get_lc(),
            |lc| lc + (E::Fr::one(), res.get_variable()),
        );

        Ok(res)
    }

    pub fn mul_by_var_with_coeff<CS>(cs: CS, num: &Self, var: &AllocatedNum<E>, coef: E::Fr) -> Result<AllocatedNum<E>, SynthesisError>
    where CS: ConstraintSystem<E> {
        
        let value = var.get_value().and_then(|mut x| {
            x.mul_assign(&coef);
            Some(x)
        });

        let temp_num = Num {
            value, 
            lc: LinearCombination::zero() + (coef, var.get_variable()),
        };
        
        Self::mul(cs, num, &temp_num)
    }

    pub fn enforce<CS: ConstraintSystem<E>>(mut cs: CS, a: &Self, b: &Self, c: &Self) 
    {
        cs.enforce(
            || "Num: enforce",
            |lc| lc + a.get_lc(),
            |lc| lc + b.get_lc(),
            |lc| lc + c.get_lc(),
        ); 
    }
}


#[cfg(test)]
mod test {
    use rand::{SeedableRng, Rand, Rng, XorShiftRng};
    use bellman::{ConstraintSystem};
    use bellman::pairing::bls12_381::{Bls12, Fr};
    use bellman::pairing::ff::{Field, PrimeField, BitIterator};
    use ::circuit::test::*;
    use super::{AllocatedNum, Boolean};

    #[test]
    fn test_allocated_num() {
        let mut cs = TestConstraintSystem::<Bls12>::new();

        AllocatedNum::alloc(&mut cs, || Ok(Fr::one())).unwrap();

        assert!(cs.get("num") == Fr::one());
    }

    #[test]
    fn test_num_squaring() {
        let mut cs = TestConstraintSystem::<Bls12>::new();

        let n = AllocatedNum::alloc(&mut cs, || Ok(Fr::from_str("3").unwrap())).unwrap();
        let n2 = n.square(&mut cs).unwrap();

        assert!(cs.is_satisfied());
        assert!(cs.get("squared num") == Fr::from_str("9").unwrap());
        assert!(n2.value.unwrap() == Fr::from_str("9").unwrap());
        cs.set("squared num", Fr::from_str("10").unwrap());
        assert!(!cs.is_satisfied());
    }

    #[test]
    fn test_limit_number_of_bits() {
        let mut cs = TestConstraintSystem::<Bls12>::new();

        let n = AllocatedNum::alloc(&mut cs, || Ok(Fr::from_str("3").unwrap())).unwrap();

        n.limit_number_of_bits(&mut cs, 2).unwrap();

        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_limit_number_of_bits_error() {
        let mut cs = TestConstraintSystem::<Bls12>::new();

        let n = AllocatedNum::alloc(&mut cs, || Ok(Fr::from_str("3").unwrap())).unwrap();

        n.limit_number_of_bits(&mut cs, 1).unwrap();
        assert!(!cs.is_satisfied());
    }

    #[test]
    fn test_num_multiplication() {
        let mut cs = TestConstraintSystem::<Bls12>::new();

        let n = AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(Fr::from_str("12").unwrap())).unwrap();
        let n2 = AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(Fr::from_str("10").unwrap())).unwrap();
        let n3 = n.mul(&mut cs, &n2).unwrap();

        assert!(cs.is_satisfied());
        assert!(cs.get("product num") == Fr::from_str("120").unwrap());
        assert!(n3.value.unwrap() == Fr::from_str("120").unwrap());
        cs.set("product num", Fr::from_str("121").unwrap());
        assert!(!cs.is_satisfied());
    }

    #[test]
    fn test_num_conditional_reversal() {
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let a = AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(rng.gen())).unwrap();
            let b = AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(rng.gen())).unwrap();
            let condition = Boolean::constant(false);
            let (c, d) = AllocatedNum::conditionally_reverse(&mut cs, &a, &b, &condition).unwrap();

            assert!(cs.is_satisfied());

            assert_eq!(a.value.unwrap(), c.value.unwrap());
            assert_eq!(b.value.unwrap(), d.value.unwrap());
        }

        {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let a = AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(rng.gen())).unwrap();
            let b = AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(rng.gen())).unwrap();
            let condition = Boolean::constant(true);
            let (c, d) = AllocatedNum::conditionally_reverse(&mut cs, &a, &b, &condition).unwrap();

            assert!(cs.is_satisfied());

            assert_eq!(a.value.unwrap(), d.value.unwrap());
            assert_eq!(b.value.unwrap(), c.value.unwrap());
        }
    }

    #[test]
    fn test_num_conditional_select() {
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let a = AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(rng.gen())).unwrap();
            let b = AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(rng.gen())).unwrap();

            let condition_true = Boolean::constant(true);
            let c = AllocatedNum::conditionally_select(cs.namespace(|| "c"), &a, &b, &condition_true).unwrap();

            let condition_false = Boolean::constant(false);
            let d = AllocatedNum::conditionally_select(cs.namespace(|| "d"), &a, &b, &condition_false).unwrap();

            assert!(cs.is_satisfied());
            assert!(cs.num_constraints() == 2);

            assert_eq!(a.value.unwrap(), c.value.unwrap());
            assert_eq!(b.value.unwrap(), d.value.unwrap());
        }
    }

    #[test]
    fn test_num_equals() {
        let mut cs = TestConstraintSystem::<Bls12>::new();

        let a = AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(Fr::from_str("10").unwrap())).unwrap();
        let b = AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(Fr::from_str("12").unwrap())).unwrap();
        let c = AllocatedNum::alloc(cs.namespace(|| "c"), || Ok(Fr::from_str("10").unwrap())).unwrap();

        let not_eq = AllocatedNum::equals(cs.namespace(|| "not_eq"), &a, &b).unwrap();
        let eq = AllocatedNum::equals(cs.namespace(|| "eq"), &a, &c).unwrap();

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 2 * 6);

        assert_eq!(not_eq.get_value().unwrap(), false);
        assert_eq!(eq.get_value().unwrap(), true);
    }

    #[test]
    fn test_num_nonzero() {
        {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let n = AllocatedNum::alloc(&mut cs, || Ok(Fr::from_str("3").unwrap())).unwrap();
            n.assert_nonzero(&mut cs).unwrap();

            assert!(cs.is_satisfied());
            cs.set("ephemeral inverse", Fr::from_str("3").unwrap());
            assert!(cs.which_is_unsatisfied() == Some("nonzero assertion constraint"));
        }
        {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let n = AllocatedNum::alloc(&mut cs, || Ok(Fr::zero())).unwrap();
            assert!(n.assert_nonzero(&mut cs).is_err());
        }
    }

    #[test]
    fn test_into_bits_strict() {
        let mut negone = Fr::one();
        negone.negate();

        let mut cs = TestConstraintSystem::<Bls12>::new();

        let n = AllocatedNum::alloc(&mut cs, || Ok(negone)).unwrap();
        n.into_bits_le_strict(&mut cs).unwrap();

        assert!(cs.is_satisfied());

        // make the bit representation the characteristic
        cs.set("bit 254/boolean", Fr::one());

        // this makes the conditional boolean constraint fail
        assert_eq!(cs.which_is_unsatisfied().unwrap(), "bit 254/boolean constraint");
    }

    #[test]
    fn test_into_bits() {
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for i in 0..200 {
            let r = Fr::rand(&mut rng);
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let n = AllocatedNum::alloc(&mut cs, || Ok(r)).unwrap();

            let bits = if i % 2 == 0 {
                n.into_bits_le(&mut cs).unwrap()
            } else {
                n.into_bits_le_strict(&mut cs).unwrap()
            };

            assert!(cs.is_satisfied());

            for (b, a) in BitIterator::new(r.into_repr()).skip(1).zip(bits.iter().rev()) {
                if let &Boolean::Is(ref a) = a {
                    assert_eq!(b, a.get_value().unwrap());
                } else {
                    unreachable!()
                }
            }

            cs.set("num", Fr::rand(&mut rng));
            assert!(!cs.is_satisfied());
            cs.set("num", r);
            assert!(cs.is_satisfied());

            for i in 0..Fr::NUM_BITS {
                let name = format!("bit {}/boolean", i);
                let cur = cs.get(&name);
                let mut tmp = Fr::one();
                tmp.sub_assign(&cur);
                cs.set(&name, tmp);
                assert!(!cs.is_satisfied());
                cs.set(&name, cur);
                assert!(cs.is_satisfied());
            }
        }
    }
}
