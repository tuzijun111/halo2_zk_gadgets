//! Lt chip can be used to compare LT for two expressions LHS and RHS.

use eth_types::Field;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Chip, Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, VirtualCells},
    poly::Rotation,
};

use super::{
    bool_check,
    util::{expr_from_bytes, pow_of_two},
};

/// Instruction that the Lt chip needs to implement.
pub trait LtEqInstruction<F: FieldExt> {
    /// Assign the lhs and rhs witnesses to the Lt chip's region.
    fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        lhs: F,
        rhs: F,
        lhs1: F,
        rhs1: F,
    ) -> Result<(), Error>;

    /// Load the u8 lookup table.
    fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error>;
}

/// Config for the Lt chip.
#[derive(Clone, Copy, Debug)]
pub struct LtEqConfig<F, const N_BYTES: usize> {
    /// Denotes the lt outcome. If lhs < rhs then lt == 1, otherwise lt == 0.
    pub lt: Column<Advice>,
    /// Denotes the bytes representation of the difference between lhs and rhs.
    pub diff: [Column<Advice>; N_BYTES],
    /// Denotes the range within which each byte should lie.
    pub u8: Column<Fixed>,
    /// Denotes the range within which both lhs and rhs lie.
    pub range: F,
}

impl<F: Field, const N_BYTES: usize> LtEqConfig<F, N_BYTES> {
    /// Returns an expression that denotes whether lhs < rhs, or not.
    pub fn is_lt(&self, meta: &mut VirtualCells<F>, rotation: Option<Rotation>) -> Expression<F> {
        meta.query_advice(self.lt, rotation.unwrap_or_else(Rotation::cur))
    }
}

/// Chip that compares lhs < rhs.
#[derive(Clone, Debug)]
pub struct LtEqChip<F, const N_BYTES: usize> {
    config: LtEqConfig<F, N_BYTES>,
}

impl<F: Field, const N_BYTES: usize> LtEqChip<F, N_BYTES> {
    /// Configures the Lt chip.
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        lhs: impl FnOnce(&mut VirtualCells<F>) -> Expression<F>,
        rhs: impl FnOnce(&mut VirtualCells<F>) -> Expression<F>,
        lhs1: impl FnOnce(&mut VirtualCells<F>) -> Expression<F>,
        rhs1: impl FnOnce(&mut VirtualCells<F>) -> Expression<F>,
    ) -> LtEqConfig<F, N_BYTES> {
        let lt = meta.advice_column();
        let diff = [(); N_BYTES].map(|_| meta.advice_column());
        let range = pow_of_two(N_BYTES * 8);
        let u8 = meta.fixed_column();


        meta.create_gate("lt gate", |meta| {
            let q_enable = q_enable(meta);
            let lt = meta.query_advice(lt, Rotation::cur());

            let diff_bytes = diff
                .iter()
                .map(|c| meta.query_advice(*c, Rotation::cur()))
                .collect::<Vec<Expression<F>>>();
            let one_expression= Expression::Constant(F::from(1));

            // // concatenate two Expression::F values:
            // let shift_amount = std::cmp::min(N_BYTES * 8, 63);
            // let con1 = lhs(meta) * F::from(1u64 << shift_amount) + rhs(meta);
            // let con2 = lhs1(meta) * F::from(1u64 << shift_amount) + rhs1(meta);
            let con1 = lhs(meta) + rhs(meta);
            let con2 = lhs1(meta) + rhs1(meta);


            let check_a =
                con1 - (con2 + one_expression)- expr_from_bytes(&diff_bytes) + (lt.clone() * range);

            let check_b = bool_check(lt);

            [check_a, check_b]
                .into_iter()
                .map(move |poly| q_enable.clone() * poly)
        });

        meta.annotate_lookup_any_column(u8, || "LOOKUP_u8");

        diff[0..N_BYTES].iter().for_each(|column| {
            meta.lookup_any("range check for u8", |meta| {
                let u8_cell = meta.query_advice(*column, Rotation::cur());
                let u8_range = meta.query_fixed(u8, Rotation::cur());
                vec![(u8_cell, u8_range)]
            });
        });

        LtEqConfig {
            lt,
            diff,
            range,
            u8,
        }
    }

    /// Constructs a Lt chip given a config.
    pub fn construct(config: LtEqConfig<F, N_BYTES>) -> LtEqChip<F, N_BYTES> {
        LtEqChip { config }
    }
}

impl<F: Field, const N_BYTES: usize> LtEqInstruction<F> for LtEqChip<F, N_BYTES> {
    fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        lhs: F,
        rhs: F,
        lhs1: F,
        rhs1: F,
    ) -> Result<(), Error> {
        let config = self.config();

        // let shift_amount = std::cmp::min(N_BYTES * 8, 63);
        // let con1 = lhs * F::from(1u64 << shift_amount) + rhs;
        // let con2 = lhs1 * F::from(1u64 << shift_amount) + rhs1;

        let con1 = lhs + rhs;
        let con2 = lhs1 + rhs1;

        let lt = con1 < (con2 + F::one());

        println!("Anything wrong here? {:?} {:?}", con1, con2);

        region.assign_advice(
            || "lt chip: lt",
            config.lt,
            offset,
            || Value::known(F::from(lt as u64)),
        )?;

        let diff = (con1 - (con2 + F::one())) + (if lt { config.range } else { F::zero() });
        let diff_bytes = diff.to_repr();
        let diff_bytes = diff_bytes.as_ref();
        for (idx, diff_column) in config.diff.iter().enumerate() {
            region.assign_advice(
                || format!("lt chip: diff byte {}", idx),
                *diff_column,
                offset,
                || Value::known(F::from(diff_bytes[idx] as u64)),
            )?;
        }

        Ok(())
    }

    fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        const RANGE: usize = 256;

        layouter.assign_region(
            || "load u8 range check table",
            |mut region| {
                for i in 0..RANGE {
                    region.assign_fixed(
                        || "assign cell in fixed column",
                        self.config.u8,
                        i,
                        || Value::known(F::from(i as u64)),
                    )?;
                }
                Ok(())
            },
        )
    }
}

impl<F: Field, const N_BYTES: usize> Chip<F> for LtEqChip<F, N_BYTES> {
    type Config = LtEqConfig<F, N_BYTES>;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

#[cfg(test)]
mod test {
    use super::{LtEqChip, LtEqConfig, LtEqInstruction};
    use eth_types::Field;
    use halo2_proofs::{
        arithmetic::FieldExt,
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        halo2curves::bn256::Fr as Fp,
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Selector},
        poly::Rotation,
    };
    use std::marker::PhantomData;

    macro_rules! try_test_circuit {
        ($values:expr, $values1:expr, $checks:expr, $result:expr) => {{
            // let k = usize::BITS - $values.len().leading_zeros();

            // TODO: remove zk blinding factors in halo2 to restore the
            // correct k (without the extra + 2).
            let k = 9;
            let circuit = TestCircuit::<Fp> {
                values: Some($values),
                values1: Some($values1),
                checks: Some($checks),
                _marker: PhantomData,
            };
            let prover = MockProver::<Fp>::run(k, &circuit, vec![]).unwrap();
            assert_eq!(prover.verify(), $result);
        }};
    }

    macro_rules! try_test_circuit_error {
        ($values:expr, $checks:expr) => {{
            // let k = usize::BITS - $values.len().leading_zeros();

            // TODO: remove zk blinding factors in halo2 to restore the
            // correct k (without the extra + 2).
            let k = 9;
            let circuit = TestCircuit::<Fp> {
                values: Some($values),
                values1: Some($values1),
                checks: Some($checks),
                _marker: PhantomData,
            };
            let prover = MockProver::<Fp>::run(k, &circuit, vec![]).unwrap();
            assert!(prover.verify().is_err());
        }};
    }

    #[test]
    fn row_diff_is_lt() {
        #[derive(Clone, Debug)]
        struct TestCircuitConfig<F> {
            q_enable: Selector,
            value: Column<Advice>,
            value1: Column<Advice>,
            check: Column<Advice>,
            lt: LtEqConfig<F, 8>,
        }

        #[derive(Default)]
        struct TestCircuit<F: FieldExt> {
            values: Option<Vec<u64>>,
            values1: Option<Vec<u64>>,
            // checks[i] = lt(values[i + 1], values[i])
            checks: Option<Vec<bool>>,
            _marker: PhantomData<F>,
        }

        impl<F: Field> Circuit<F> for TestCircuit<F> {
            type Config = TestCircuitConfig<F>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                let q_enable = meta.complex_selector();
                let value = meta.advice_column();
                let value1 = meta.advice_column();
                let check = meta.advice_column();

                let lt = LtEqChip::configure(
                    meta,
                    |meta| meta.query_selector(q_enable),
                    |meta| meta.query_advice(value, Rotation::prev()),
                    |meta| meta.query_advice(value1, Rotation::prev()),
                    |meta| meta.query_advice(value, Rotation::cur()),
                    |meta| meta.query_advice(value1, Rotation::cur()),
                );

                let config = Self::Config {
                    q_enable,
                    value,
                    value1,
                    check,
                    lt,
                };

                meta.create_gate("check is_lt between adjacent rows", |meta| {
                    let q_enable = meta.query_selector(q_enable);

                    // This verifies lt(value::cur, value::next) is calculated correctly
                    let check = meta.query_advice(config.check, Rotation::cur());
                   

                    vec![q_enable * (config.lt.is_lt(meta, None) - check)]
                });

                config
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                let chip = LtEqChip::construct(config.lt);

                let values: Vec<_> = self
                    .values
                    .as_ref()
                    .map(|values| values.iter().map(|value| F::from(*value)).collect())
                    .ok_or(Error::Synthesis)?;
                let values1: Vec<_> = self
                    .values1
                    .as_ref()
                    .map(|values1| values1.iter().map(|value1| F::from(*value1)).collect())
                    .ok_or(Error::Synthesis)?;
                let checks = self.checks.as_ref().ok_or(Error::Synthesis)?;
                let (first_value, values) = values.split_at(1);
                let (first_value1, values1) = values1.split_at(1);
                let first_value = first_value[0];
                let first_value1 = first_value1[0];
               

                chip.load(&mut layouter)?;

                layouter.assign_region(
                    || "witness",
                    |mut region| {
                        region.assign_advice(
                            || "first row value",
                            config.value,
                            0,
                            || Value::known(first_value),
                        )?;

                        region.assign_advice(
                            || "first row value1",
                            config.value1,
                            0,
                            || Value::known(first_value1),
                        )?;

                        

                        let mut value_prev = first_value;
                        let mut value_prev1 = first_value1;
                        
                        
                        for (idx, ((value, value1), check)) in values.iter().zip(values1.iter()).zip(checks).enumerate() {
                            config.q_enable.enable(&mut region, idx + 1)?;
                            region.assign_advice(
                                || "check",
                                config.check,
                                idx + 1,
                                || Value::known(F::from(*check as u64)),
                            )?;
                            region.assign_advice(
                                || "value",
                                config.value,
                                idx + 1,
                                || Value::known(*value),
                            )?;
                            region.assign_advice(
                                || "value",
                                config.value1,
                                idx + 1,
                                || Value::known(*value1),
                            )?;
                            chip.assign(&mut region, idx + 1, value_prev, value_prev1,  *value, *value1)?;

                            value_prev = *value;
                            value_prev1 = *value1;
                        }

                        Ok(())
                    },
                )
            }
        }

        // ok
        try_test_circuit!(vec![1, 2, 3, 4], vec![5, 6, 7, 8], vec![true, true, true, true], Ok(()));
        // try_test_circuit!(vec![1, 2, 1, 3, 2], vec![true, false, true, false], Ok(()));
        // // error
        // try_test_circuit_error!(vec![5, 4, 3, 2, 1], vec![true, true, true, true]);
        // try_test_circuit_error!(vec![1, 2, 1, 3, 2], vec![false, true, false, true]);
    }

    
}
