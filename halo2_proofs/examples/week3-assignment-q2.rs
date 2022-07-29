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

trait FuncInstructions<F: FieldExt>: CalculateInstructions<F> {
    /// Variable representing a number.
    type Num;

    /// Loads a number into the circuit as a private input.
    fn load_private(
        &self,
        layouter: impl Layouter<F>,
        a: Option<F>,
    ) -> Result<<Self as FuncInstructions<F>>::Num, Error>;

    /// Batch load
    fn load_privates(
        &self,
        layouter: impl Layouter<F>,
        a: Option<Vec<F>>,
    ) -> Result<Vec<<Self as FuncInstructions<F>>::Num>, Error>;

    //
    // def bit_add(a int[256], b int[256]):
    //   o = int[256]
    //   cr = 0
    //   for i in 1..256
    //      sum_i = a[i] + b[i]
    //      o[i] = (sum_i & 0x1) + cr
    //      cr = sum_i & 0x2
    //   assert cr == 0
    //   return o
    // }
    //
    fn bit_calculate(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &Vec<<Self as FuncInstructions<F>>::Num>,
        b: &Vec<<Self as FuncInstructions<F>>::Num>,
    ) -> Result<Vec<<Self as FuncInstructions<F>>::Num>, Error>;

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

    // a + b
    fn calculate_a_xor_b(
        &self,
        layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error>;

    // a * b
    fn calculate_a_mul_b(
        &self,
        layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error>;
}
// ANCHOR_END: plonk-instructions

// ANCHOR: field-config
// The top-level config that provides all necessary columns and permutations
// for the other configs.
#[derive(Clone, Debug)]
struct FieldConfig {
    /// Public inputs
    instance: Column<Instance>,

    plonk_config: PlonkConfig,

    size: usize,
}
// ANCHOR END: field-config

// ANCHOR: field-chip
/// The top-level chip that will implement the `FieldInstructions`.
struct FieldChip<F: FieldExt> {
    config: FieldConfig,
    _marker: PhantomData<F>,
}
// ANCHOR_END: field-chip

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

// ANCHOR: r1cs-chip-impl
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
// ANCHOR_END: r1cs-chip-impl

// ANCHOR: r1cs-instructions-impl
impl<F: FieldExt> CalculateInstructions<F> for FieldChip<F> {
    type Num = Number<F>;

    fn calculate_a_xor_b(
        &self,
        layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error> {
        let config = self.config().plonk_config.clone();
        let plonk_chip = BasicPlonkChip::<F>::construct(config, ());
        plonk_chip.calculate_a_xor_b(layouter, a, b)
    }

    fn calculate_a_mul_b(
        &self,
        layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error> {
        let config = self.config().plonk_config.clone();
        let plonk_chip = BasicPlonkChip::<F>::construct(config, ());
        plonk_chip.calculate_a_mul_b(layouter, a, b)
    }
}

impl<F: FieldExt> CalculateInstructions<F> for BasicPlonkChip<F> {
    type Num = Number<F>;

    fn calculate_a_mul_b(
        &self,
        mut layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter.assign_region(
            || "calc a*b",
            |mut region| {
                a.0.copy_advice(|| "lhs", &mut region, config.a, 0)?;
                b.0.copy_advice(|| "rhs", &mut region, config.b, 0)?;
                let value = a.0.value().and_then(|a| b.0.value().map(|b| *a * *b));

                let out = region.assign_advice(|| "out", self.config.c, 0, || value)?;

                region.assign_fixed(|| "sa", self.config.sa, 0, || Value::known(F::zero()))?;
                region.assign_fixed(|| "sb", self.config.sb, 0, || Value::known(F::zero()))?;
                region.assign_fixed(|| "sc", self.config.sc, 0, || Value::known(F::one()))?;
                region.assign_fixed(|| "sq", self.config.sq, 0, || Value::known(F::zero()))?;
                region.assign_fixed(|| "s(a * b)", self.config.sm, 0, || Value::known(F::one()))?;

                Ok(Number(out))
            },
        )
    }

    /// XOR(a, b) == a + b - 2ab
    fn calculate_a_xor_b(
        &self,
        mut layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter.assign_region(
            || "calc a ^ b",
            |mut region| {
                a.0.copy_advice(|| "lhs", &mut region, config.a, 0)?;
                b.0.copy_advice(|| "rhs", &mut region, config.b, 0)?;
                let value = a.0.value().and_then(|a| {
                    b.0.value()
                        .map(|b| *a + *b - (F::one() + F::one()) * *a * *b)
                });

                let out = region.assign_advice(|| "out", self.config.c, 0, || value)?;

                region.assign_fixed(|| "sa", self.config.sa, 0, || Value::known(F::one()))?;
                region.assign_fixed(|| "sb", self.config.sb, 0, || Value::known(F::one()))?;
                region.assign_fixed(|| "sc", self.config.sc, 0, || Value::known(F::one()))?;
                region.assign_fixed(|| "sq", self.config.sq, 0, || Value::known(F::zero()))?;
                region.assign_fixed(
                    || "s(a * b)",
                    self.config.sm,
                    0,
                    || Value::known(-(F::one() + F::one())),
                )?;

                Ok(Number(out))
            },
        )
    }
}
// ANCHOR END: r1cs-instructions-impl

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

    fn configure(meta: &mut ConstraintSystem<F>) -> <Self as Chip<F>>::Config {
        // We also need an instance column to store public inputs.
        let instance = meta.instance_column();
        let plonk_config = BasicPlonkChip::configure(meta);

        meta.enable_equality(instance);
        FieldConfig {
            instance,
            plonk_config,
            size: 256 as usize,
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
                        config.plonk_config.a,
                        0,
                        || value.map(|v| Value::known(v)).unwrap(),
                    )
                    .map(Number)
            },
        )
    }

    fn load_privates(
        &self,
        mut layouter: impl Layouter<F>,
        value: Option<Vec<F>>,
    ) -> Result<Vec<<Self as FuncInstructions<F>>::Num>, Error> {
        let config = self.config();

        let mut o = vec![];
        match value {
            Some(values) => {
                for (i, v) in values.iter().enumerate() {
                    o.push(layouter.assign_region(
                        || "load private",
                        |mut region| {
                            region
                                .assign_advice(
                                    || "private input",
                                    config.plonk_config.a,
                                    i,
                                    || Value::known(*v),
                                )
                                .map(Number)
                        },
                    )?);
                }
            }
            None => panic!("wrong values"),
        }
        Ok(o)
    }

    fn bit_calculate(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &Vec<<Self as FuncInstructions<F>>::Num>,
        b: &Vec<<Self as FuncInstructions<F>>::Num>,
    ) -> Result<Vec<<Self as FuncInstructions<F>>::Num>, Error> {
        let mut output = vec![];

        let mut a_bit = &a[0];
        let mut b_bit = &b[0];
        let mut a_plus_b = self.calculate_a_xor_b(
            layouter.namespace(|| "c0 = a0 xor b0"),
            a_bit.clone(),
            b_bit.clone(),
        )?;
        output.push(a_plus_b);
        let mut cr = self.calculate_a_mul_b(
            layouter.namespace(|| "cr0 = a0*b0"),
            a_bit.clone(),
            b_bit.clone(),
        )?;

        for i in 1..self.config.size {
            a_bit = &a[i];
            b_bit = &b[i];

            a_plus_b = self.calculate_a_xor_b(
                layouter.namespace(|| "a xor b"),
                a_bit.clone(),
                b_bit.clone(),
            )?;
            let a_b_cr = self.calculate_a_xor_b(
                layouter.namespace(|| "o[i] = a[i]+b[i]+cr[i-1]"),
                a_plus_b.clone(),
                cr.clone(),
            )?;
            output.push(a_b_cr.clone());

            let _ab =
                self.calculate_a_mul_b(layouter.namespace(|| "a*b"), a_bit.clone(), b_bit.clone())?;
            let _ac =
                self.calculate_a_mul_b(layouter.namespace(|| "a*cr"), a_bit.clone(), cr.clone())?;
            let _bc =
                self.calculate_a_mul_b(layouter.namespace(|| "b*cr"), cr.clone(), b_bit.clone())?;

            let cr_0 = self.calculate_a_xor_b(
                layouter.namespace(|| "a*b ^ a*cr"),
                _ab.clone(),
                _ac.clone(),
            )?;
            cr = self.calculate_a_xor_b(
                layouter.namespace(|| "cr = a*b ^ a*cr ^ b*cr"),
                cr_0.clone(),
                _bc.clone(),
            )?;
        }
        Ok(output)
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
    a: Option<Vec<F>>,
    b: Option<Vec<F>>,
    // c: Option<Vec<F>>,
}

impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
    // Since we are using a single chip for everything, we can just reuse its config.
    type Config = FieldConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        FieldChip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let field_chip = FieldChip::<F>::construct(config, ());

        // Load our private values into the circuit.
        let x = &field_chip.load_privates(layouter.namespace(|| "load a"), self.a.clone())?;
        let y = &field_chip.load_privates(layouter.namespace(|| "load b"), self.b.clone())?;

        let d = field_chip.bit_calculate(&mut layouter, x, y)?;

        // Expose the result as a public input to the circuit.
        for (i, v) in d.iter().enumerate() {
            field_chip.expose_public(layouter.namespace(|| "expose a+b"), v.clone(), i)?;
        }
        Ok(())
    }
}
// ANCHOR_END: circuit

#[allow(clippy::many_single_char_names)]
fn main() {
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::pasta::Fp;

    fn i_to_b(x: [u64; 4]) -> Vec<Fp> {
        let mut o = vec![];
        for i in 0..64 {
            o.push(Fp::from((x[0] & (1u64 << i) != 0) as u64));
        }

        for i in 0..64 {
            o.push(Fp::from((x[1] & (1u64 << i) != 0) as u64));
        }

        for i in 0..64 {
            o.push(Fp::from((x[2] & (1u64 << i) != 0) as u64));
        }

        for i in 0..64 {
            o.push(Fp::from((x[3] & (1u64 << i) != 0) as u64));
        }

        o
    }

    // ANCHOR: test-circuit
    // The number of rows in our circuit cannot exceed 2^k. Since our example
    // circuit is very small, we can pick a very small value here.
    let k = 20;

    // Prepare the private and public inputs to the circuit!
    let a = 7;
    let b = 1;

    // Instantiate the circuit with the private inputs.
    let circuit = MyCircuit {
        a: Some(i_to_b([a, 0, 0, 0])),
        b: Some(i_to_b([b, 0, 0, 0])),
        // c: Some(i_to_b(a + b)),
    };

    // Arrange the public input. We expose the function result in row 0
    // of the instance column, so we position it there in our public inputs.
    let mut public_inputs = i_to_b([a + b, 0, 0, 0]);
    println!("{:?}", public_inputs);

    // Given the correct public input, our circuit will verify.
    let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();
    let err = prover.verify();
    if err.is_err() {
        for e in err.err().iter() {
            for s in e.iter() {
                println!("{}", s);
            }
        }
    }
    // assert_eq!(err, Ok(()));

    // If we try some other public input, the proof will fail!
    // public_inputs[0] += Fp::one();
    // let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();
    // assert!(prover.verify().is_err());
    // ANCHOR_END: test-circuit
}
