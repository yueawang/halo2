use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Chip, Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Instance, Selector,
    },
    poly::Rotation,
};

// ANCHOR: field-instructions
/// A variable representing a number.
#[derive(Clone)]
struct Number<F: FieldExt>(AssignedCell<F, F>);

// ANCHOR: is_zero-instructions
trait ConditionInstructions<F: FieldExt>: Chip<F> {
    /// Variable representing a number.
    type Num;

    /// Returns `x == 0`.
    fn is_zero(&self, layouter: impl Layouter<F>, a: Self::Num) -> Result<Self::Num, Error>;
}
// ANCHOR_END: is_zero-instructions

trait FuncInstructions<F: FieldExt>: ConditionInstructions<F> + CalculateInstructions<F> {
    /// Variable representing a number.
    type Num;

    /// Loads a number into the circuit as a private input.
    fn load_private(
        &self,
        layouter: impl Layouter<F>,
        a: Option<F>,
    ) -> Result<<Self as FuncInstructions<F>>::Num, Error>;

    //
    // def f(x, y, z):
    //   if x == 1:
    //     return y*z
    //   return 2y - z
    // }
    //
    fn conditional_calculate(
        &self,
        layouter: &mut impl Layouter<F>,
        a: <Self as FuncInstructions<F>>::Num,
        b: <Self as FuncInstructions<F>>::Num,
        c: <Self as FuncInstructions<F>>::Num,
    ) -> Result<<Self as FuncInstructions<F>>::Num, Error>;

    /// Exposes a number as a public input to the circuit.
    fn expose_public(
        &self,
        layouter: impl Layouter<F>,
        num: <Self as FuncInstructions<F>>::Num,
        row: usize,
    ) -> Result<(), Error>;
}
// ANCHOR_END: field-instructions

// ANCHOR: plonk-instructions
trait CalculateInstructions<F: FieldExt>: Chip<F> {
    /// Variable representing a number.
    type Num;

    /// 2*a - b
    fn calculate_2amb(
        &self,
        layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error>;

    // a - 1
    fn calculate_am1(&self, layouter: impl Layouter<F>, a: Self::Num) -> Result<Self::Num, Error>;

    // a * b
    fn calculate_ab(
        &self,
        layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error>;

    // a + b
    fn calculate_a_plus_b(
        &self,
        layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error>;

    // !a
    fn calculate_not_a(&self, layouter: impl Layouter<F>, a: Self::Num)
        -> Result<Self::Num, Error>;
}
// ANCHOR_END: plonk-instructions

// ANCHOR: field-config
// The top-level config that provides all necessary columns and permutations
// for the other configs.
#[derive(Clone, Debug)]
struct FieldConfig {
    /// Public inputs
    instance: Column<Instance>,

    cond_config: ConditionConfig,
    plonk_config: PlonkConfig,
}
// ANCHOR END: field-config

// ANCHOR: is_zero-config
#[derive(Clone, Debug)]
struct ConditionConfig {
    advice: [Column<Advice>; 2],
    s_cond: Selector,
}
// ANCHOR_END: is_zero-config

// ANCHOR: field-chip
/// The top-level chip that will implement the `FieldInstructions`.
struct FieldChip<F: FieldExt> {
    config: FieldConfig,
    _marker: PhantomData<F>,
}
// ANCHOR_END: field-chip

// ANCHOR: is_zero-chip
struct ConditionChip<F: FieldExt> {
    config: ConditionConfig,
    _marker: PhantomData<F>,
}
// ANCHOR END: is_zero-chip

// ANCHOR: is_zero-chip-trait-impl
impl<F: FieldExt> Chip<F> for ConditionChip<F> {
    type Config = ConditionConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
// ANCHOR END: is_zero-chip-trait-impl

// ANCHOR: is_zero-chip-impl
impl<F: FieldExt> ConditionChip<F> {
    fn construct(config: <Self as Chip<F>>::Config, _loaded: <Self as Chip<F>>::Loaded) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        advice: [Column<Advice>; 2],
    ) -> <Self as Chip<F>>::Config {
        let s_cond = meta.selector();

        // Define our is_zero gate!
        meta.create_gate("a == 0", |meta| {
            let a = meta.query_advice(advice[0], Rotation::cur());
            let a_inv = meta.query_advice(advice[1], Rotation::cur());
            let a_is_zero = meta.query_advice(advice[0], Rotation::next());
            let s_cond = meta.query_selector(s_cond);

            let one = Expression::Constant(F::one());

            let is_zero_expression = one - a.clone() * a_inv.clone();

            // This checks `value_inv ≡ value.invert()` when `value` is not
            // zero: value ⋅ (1 - value ⋅ value_inv)
            let poly1 = a * is_zero_expression.clone();
            // This checks `value_inv ≡ 0` when `value` is zero:
            // value_inv ⋅ (1 - value ⋅ value_inv)
            let poly2 = a_inv * is_zero_expression.clone();

            vec![
                s_cond.clone() * poly1,
                s_cond.clone() * poly2,
                s_cond.clone() * (a_is_zero - is_zero_expression),
            ]
        });

        ConditionConfig { advice, s_cond }
    }
}
// ANCHOR END: is_zero-chip-impl


// ANCHOR: is_zero-instructions-impl
impl<F: FieldExt> ConditionInstructions<F> for FieldChip<F> {
    type Num = Number<F>;
    fn is_zero(&self, layouter: impl Layouter<F>, a: Self::Num) -> Result<Self::Num, Error> {
        let config = self.config().cond_config.clone();

        let condition_chip = ConditionChip::<F>::construct(config, ());
        condition_chip.is_zero(layouter, a)
    }
}

impl<F: FieldExt> ConditionInstructions<F> for ConditionChip<F> {
    type Num = Number<F>;

    fn is_zero(&self, mut layouter: impl Layouter<F>, a: Self::Num) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter.assign_region(
            || "a == 0",
            |mut region: Region<'_, F>| {
                // We only want to use a single is_zero gate in this region,
                // so we enable it at region offset 0; this means it will constrain
                // cells at offsets 0 and 1.
                config.s_cond.enable(&mut region, 0)?;

                // The inputs we've been given could be located anywhere in the circuit,
                // but we can only rely on relative offsets inside this region. So we
                // assign new cells inside the region and constrain them to have the
                // same values as the inputs.
                a.0.copy_advice(|| "a", &mut region, config.advice[0], 0)?;

                let a_inv = a.0.value().map(|v| v.invert().unwrap_or_else(|| F::zero()));
                region.assign_advice(
                    || "a_inv",
                    config.advice[1],
                    0,
                    || a_inv,
                )?;

                // Now we can compute the is_zero result, which is to be assigned
                // into the output position.
                let value = a.0.value().and_then(|a| a_inv.map(|ai| F::one() - *a * ai));

                // Finally, we do the assignment to the output, returning a
                // variable to be used in another part of the circuit.
                region
                    .assign_advice(
                        || "(a == 0)",
                        config.advice[0],
                        1,
                        || value,
                    )
                    .map(Number)
            },
        )
    }
}
// ANCHOR END: is_zero-instructions-impl

// ANCHOR: plonk-chip
struct BasicPlonkChip<F: FieldExt> {
  config: PlonkConfig,
  _marker: PhantomData<F>,
}
// ANCHOR_END: plonk-chip

// ANCHOR: plonk-chip-trait-impl
impl<F: FieldExt> Chip<F> for BasicPlonkChip<F> {
    type Config = PlonkConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
// ANCHOR END: plonk-chip-trait-impl
// sa * a + sb * b + sm * a * b + sq == sc * c
#[derive(Clone, Debug)]
struct PlonkConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,

    sa: Column<Fixed>,
    sb: Column<Fixed>,
    sc: Column<Fixed>,
    sm: Column<Fixed>,
    sq: Column<Fixed>,
}

// ANCHOR: plonk-chip-impl
impl<F: FieldExt> BasicPlonkChip<F> {
    fn construct(config: <Self as Chip<F>>::Config, _loaded: <Self as Chip<F>>::Loaded) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> <Self as Chip<F>>::Config {
        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();

        meta.enable_equality(a);
        meta.enable_equality(b);
        meta.enable_equality(c);

        let sm = meta.fixed_column();
        let sa = meta.fixed_column();
        let sb = meta.fixed_column();
        let sc = meta.fixed_column();
        let sq = meta.fixed_column();

        meta.create_gate("mini plonk", |meta| {
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());

            let sa = meta.query_fixed(sa, Rotation::cur());
            let sb = meta.query_fixed(sb, Rotation::cur());
            let sc = meta.query_fixed(sc, Rotation::cur());
            let sm = meta.query_fixed(sm, Rotation::cur());
            let sq = meta.query_fixed(sq, Rotation::cur());

            vec![a.clone() * sa + b.clone() * sb + a * b * sm + sq + (c * sc * (-F::one()))]
        });

        PlonkConfig {
            a,
            b,
            c,
            sa,
            sb,
            sc,
            sm,
            sq,
        }
    }
}
// ANCHOR_END: plonk-chip-impl

// ANCHOR: plonk-instructions-impl
impl<F: FieldExt> CalculateInstructions<F> for FieldChip<F> {
    type Num = Number<F>;
    fn calculate_2amb(
        &self,
        layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error> {
        let config = self.config().plonk_config.clone();
        let plonk_chip = BasicPlonkChip::<F>::construct(config, ());
        plonk_chip.calculate_2amb(layouter, a, b)
    }

    fn calculate_ab(
        &self,
        layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error> {
        let config = self.config().plonk_config.clone();
        let plonk_chip = BasicPlonkChip::<F>::construct(config, ());
        plonk_chip.calculate_ab(layouter, a, b)
    }

    fn calculate_a_plus_b(
        &self,
        layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error> {
        let config = self.config().plonk_config.clone();
        let plonk_chip = BasicPlonkChip::<F>::construct(config, ());
        plonk_chip.calculate_a_plus_b(layouter, a, b)
    }

    fn calculate_am1(&self, layouter: impl Layouter<F>, a: Self::Num) -> Result<Self::Num, Error> {
        let config = self.config().plonk_config.clone();
        let plonk_chip = BasicPlonkChip::<F>::construct(config, ());
        plonk_chip.calculate_am1(layouter, a)
    }

    fn calculate_not_a(
        &self,
        layouter: impl Layouter<F>,
        a: Self::Num,
    ) -> Result<Self::Num, Error> {
        let config = self.config().plonk_config.clone();
        let plonk_chip = BasicPlonkChip::<F>::construct(config, ());
        plonk_chip.calculate_not_a(layouter, a)
    }
}

impl<F: FieldExt> CalculateInstructions<F> for BasicPlonkChip<F> {
    type Num = Number<F>;

    fn calculate_2amb(
        &self,
        mut layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter.assign_region(
            || "2a - b",
            |mut region| {
                a.0.copy_advice(|| "lhs", &mut region, config.a, 0)?;
                b.0.copy_advice(|| "rhs", &mut region, config.b, 0)?;

                let value =
                    a.0.value()
                        .and_then(|a| b.0.value().map(|b| (*a + *a) - *b));

                let out = region.assign_advice(
                    || "out",
                    self.config.c,
                    0,
                    || value,
                )?;

                region.assign_fixed(|| "2a", self.config.sa, 0, || Value::known(F::one() + F::one()))?;
                region.assign_fixed(|| "b", self.config.sb, 0, || Value::known(-F::one()))?;
                region.assign_fixed(|| "c", self.config.sc, 0, || Value::known(F::one()))?;
                region.assign_fixed(|| "a * b", self.config.sm, 0, || Value::known(F::zero()))?;

                Ok(Number(out))
            },
        )
    }

    fn calculate_ab(
        &self,
        mut layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter.assign_region(
            || "a*b",
            |mut region| {
                a.0.copy_advice(|| "lhs", &mut region, config.a, 0)?;
                b.0.copy_advice(|| "rhs", &mut region, config.b, 0)?;

                let value = a.0.value().and_then(|a| b.0.value().map(|b| *a * *b));

                let out = region.assign_advice(
                    || "out",
                    self.config.c,
                    0,
                    || value,
                )?;

                region.assign_fixed(|| "a", self.config.sa, 0, || Value::known(F::zero()))?;
                region.assign_fixed(|| "b", self.config.sb, 0, || Value::known(F::zero()))?;
                region.assign_fixed(|| "c", self.config.sc, 0, || Value::known(F::one()))?;
                region.assign_fixed(|| "a * b", self.config.sm, 0, || Value::known(F::one()))?;

                Ok(Number(out))
            },
        )
    }

    fn calculate_a_plus_b(
        &self,
        mut layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter.assign_region(
            || "a*b",
            |mut region| {
                a.0.copy_advice(|| "lhs", &mut region, config.a, 0)?;
                b.0.copy_advice(|| "rhs", &mut region, config.b, 0)?;

                let value = a.0.value().and_then(|a| b.0.value().map(|b| *a + *b));

                let out = region.assign_advice(
                    || "out",
                    self.config.c,
                    0,
                    || value,
                )?;

                region.assign_fixed(|| "sa", self.config.sa, 0, || Value::known(F::one()))?;
                region.assign_fixed(|| "sb", self.config.sb, 0, || Value::known(F::one()))?;
                region.assign_fixed(|| "sc", self.config.sc, 0, || Value::known(F::one()))?;
                region.assign_fixed(|| "s(a * b)", self.config.sm, 0, || Value::known(F::zero()))?;

                Ok(Number(out))
            },
        )
    }

    fn calculate_am1(
        &self,
        mut layouter: impl Layouter<F>,
        a: Self::Num,
    ) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter.assign_region(
            || "a-1",
            |mut region| {
                a.0.copy_advice(|| "lhs", &mut region, config.a, 0)?;

                let value = a.0.value().map(|x| *x - F::one());

                let out = region.assign_advice(
                    || "out",
                    self.config.c,
                    0,
                    || value,
                )?;

                region.assign_fixed(|| "a", self.config.sa, 0, || Value::known(F::one()))?;
                region.assign_fixed(|| "b", self.config.sb, 0, || Value::known(F::zero()))?;
                region.assign_fixed(|| "c", self.config.sc, 0, || Value::known(F::one()))?;
                region.assign_fixed(|| "a * b", self.config.sm, 0, || Value::known(F::zero()))?;
                region.assign_fixed(|| "sq", self.config.sq, 0, || Value::known(-F::one()))?;

                Ok(Number(out))
            },
        )
    }

    fn calculate_not_a(
        &self,
        mut layouter: impl Layouter<F>,
        a: Self::Num,
    ) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter.assign_region(
            || "not a",
            |mut region| {
                a.0.copy_advice(|| "lhs", &mut region, config.a, 0)?;

                let value = a.0.value().map(|a| F::one() - *a);
                let out = region.assign_advice(
                    || "out",
                    self.config.c,
                    0,
                    || value,
                )?;

                region.assign_fixed(|| "a", self.config.sa, 0, || Value::known(-F::one()))?;
                region.assign_fixed(|| "b", self.config.sb, 0, || Value::known(F::zero()))?;
                region.assign_fixed(|| "c", self.config.sc, 0, || Value::known(F::one()))?;
                region.assign_fixed(|| "a * b", self.config.sm, 0, || Value::known(F::zero()))?;
                region.assign_fixed(|| "q", self.config.sq, 0, || Value::known(F::one()))?;

                Ok(Number(out))
            },
        )
    }
}
// ANCHOR END: plonk-instructions-impl

// ANCHOR: field-chip-trait-impl
impl<F: FieldExt> Chip<F> for FieldChip<F> {
    type Config = FieldConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
// ANCHOR_END: field-chip-trait-impl

// ANCHOR: field-chip-impl
impl<F: FieldExt> FieldChip<F> {
    fn construct(config: <Self as Chip<F>>::Config, _loaded: <Self as Chip<F>>::Loaded) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        advice: [Column<Advice>; 2],
        instance: Column<Instance>,
    ) -> <Self as Chip<F>>::Config {
        let cond_config = ConditionChip::configure(meta, advice);
        let plonk_config = BasicPlonkChip::configure(meta);

        meta.enable_equality(advice[0]);
        meta.enable_equality(advice[1]);
        meta.enable_equality(instance);

        FieldConfig {
            instance,
            cond_config,
            plonk_config,
        }
    }
}
// ANCHOR_END: field-chip-impl

// ANCHOR: field-instructions-impl
impl<F: FieldExt> FuncInstructions<F> for FieldChip<F> {
    type Num = Number<F>;

    fn load_private(
        &self,
        mut layouter: impl Layouter<F>,
        value: Option<F>,
    ) -> Result<<Self as FuncInstructions<F>>::Num, Error> {
        let config = self.config();

        layouter.assign_region(
            || "load private",
            |mut region| {
                region
                    .assign_advice(
                        || "private input",
                        config.cond_config.advice[0],
                        0,
                        || value.map(|v| Value::known(v)).unwrap(),
                    )
                    .map(Number)
            },
        )
    }

    fn conditional_calculate(
        &self,
        layouter: &mut impl Layouter<F>,
        a: <Self as FuncInstructions<F>>::Num,
        b: <Self as FuncInstructions<F>>::Num,
        c: <Self as FuncInstructions<F>>::Num,
    ) -> Result<<Self as FuncInstructions<F>>::Num, Error> {
        let x_sub_1 = self.calculate_am1(layouter.namespace(|| "x-1"), a)?;
        let x_eq_1 = self.is_zero(layouter.namespace(|| "x-1==0"), x_sub_1)?;
        let x_not_eq_1 = self.calculate_not_a(layouter.namespace(|| "x-1!=0"), x_eq_1.clone())?;
        let v1 = self.calculate_ab(layouter.namespace(|| "y*z"), b.clone(), c.clone())?;
        let v2 = self.calculate_2amb(layouter.namespace(|| "2y-z"), b.clone(), c.clone())?;
        let v3 = self.calculate_ab(layouter.namespace(|| "(x==1) * y*z"), x_eq_1.clone(), v1)?;
        let v4 = self.calculate_ab(layouter.namespace(|| "(x!=1) * (2y-z)"), x_not_eq_1, v2)?;
        self.calculate_a_plus_b(layouter.namespace(|| "f(x, y, z)"), v3, v4)
    }

    fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        num: <Self as FuncInstructions<F>>::Num,
        row: usize,
    ) -> Result<(), Error> {
        let config = self.config();

        layouter.constrain_instance(num.0.cell(), config.instance, row)
    }
}
// ANCHOR_END: field-instructions-impl

// ANCHOR: circuit
/// The full circuit implementation.
///
/// In this struct we store the private input variables. We use `Option<F>` because
/// they won't have any value during key generation. During proving, if any of these
/// were `None` we would get an error.
#[derive(Default)]
struct MyCircuit<F: FieldExt> {
    x: Option<F>,
    y: Option<F>,
    z: Option<F>,
}

impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
    // Since we are using a single chip for everything, we can just reuse its config.
    type Config = FieldConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        // We create the two advice columns that FieldChip uses for I/O.
        let advice = [meta.advice_column(), meta.advice_column()];

        // We also need an instance column to store public inputs.
        let instance = meta.instance_column();

        FieldChip::configure(meta, advice, instance)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let field_chip = FieldChip::<F>::construct(config, ());

        // Load our private values into the circuit.
        let x = field_chip.load_private(layouter.namespace(|| "load x"), self.x)?;
        let y = field_chip.load_private(layouter.namespace(|| "load y"), self.y)?;
        let z = field_chip.load_private(layouter.namespace(|| "load z"), self.z)?;

        let d = field_chip.conditional_calculate(&mut layouter, x, y, z)?;

        // Expose the result as a public input to the circuit.
        field_chip.expose_public(layouter.namespace(|| "expose d"), d, 0)
    }
}
// ANCHOR_END: circuit

fn foo(x: u64, y: u64, z: u64) -> u64 {
    if x == 1 {
        y * z
    } else {
        2 * y - z
    }
}

#[allow(clippy::many_single_char_names)]
fn main() {
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::pasta::Fp;

    // ANCHOR: test-circuit
    // The number of rows in our circuit cannot exceed 2^k. Since our example
    // circuit is very small, we can pick a very small value here.
    let k = 4;

    // Prepare the private and public inputs to the circuit!
    let a = 1;
    let b = 2;
    let c = 5;
    let d = foo(a, b, c);

    // Instantiate the circuit with the private inputs.
    let circuit = MyCircuit {
        x: Some(Fp::from(a)),
        y: Some(Fp::from(b)),
        z: Some(Fp::from(c)),
    };

    // Arrange the public input. We expose the function result in row 0
    // of the instance column, so we position it there in our public inputs.
    let mut public_inputs = vec![Fp::from(d)];

    // Given the correct public input, our circuit will verify.
    let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
    assert_eq!(prover.verify(), Ok(()));

    // If we try some other public input, the proof will fail!
    public_inputs[0] += Fp::one();
    let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();
    assert!(prover.verify().is_err());
    // ANCHOR_END: test-circuit
}
