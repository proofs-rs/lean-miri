//! Executes the pinned rustc_apfloat dependency, not host floating arithmetic.
use rustc_apfloat::{Float, FloatConvert};
use rustc_apfloat::ieee::{Half, Single, Double, Quad};
fn corpus<F: Float>() -> Vec<F> {
    let frac = F::PRECISION-1;
    let exp_bits = F::BITS-frac-1;
    let sign = 1u128 << (F::BITS-1);
    let inf = ((1u128 << exp_bits)-1) << frac;
    let bias = (1u128 << (exp_bits-1))-1;
    let one = bias << frac;
    let mut values = vec![0, sign, 1, sign+1, (1<<frac)-1, 1<<frac,
     one-1, one, one+1, one+(1<<(frac-1)), one+(1<<frac),
     inf-1, inf, inf+1, inf+(1<<(frac-1)), inf+(1<<(frac-1))+1,
     sign+inf, sign+inf+1, sign+one, sign+one+1];
    let mut seed = 81985529216486895u128;
    for _ in 0..8 {
        seed = seed.wrapping_mul(47026247687942121848144207491837523525)
            .wrapping_add(117397592171526113268558934119004209487) & (u128::MAX >> (128-F::BITS));
        values.push(seed);
    }
    values.into_iter().map(F::from_bits).collect()
}
fn run<F>() where F: Float + FloatConvert<Half> + FloatConvert<Single> + FloatConvert<Double> + FloatConvert<Quad> {
    let values = corpus::<F>();
    for &l in &values {
        for &r in &values {
            for value in [(l+r).value, (l-r).value, (l*r).value, (l/r).value, (l%r).value] {
                // MIR adjust_nan with nondeterminism disabled returns F::NAN.
                println!("{}", if value.is_nan() { F::NAN } else { value }.to_bits());
            }
            for value in [l==r, l!=r, l<r, l<=r, l>r, l>=r] { println!("{}", value as u8); }
        }
    }
    for &value in &values {
        println!("{}", (-value).to_bits());
        for width in [8,16,32,64,128] {
            println!("{}", value.to_i128(width).value);
            println!("{}", value.to_u128(width).value);
        }
        let converted: Half = value.convert(&mut false).value; println!("{}", converted.to_bits());
        let converted: Single = value.convert(&mut false).value; println!("{}", converted.to_bits());
        let converted: Double = value.convert(&mut false).value; println!("{}", converted.to_bits());
        let converted: Quad = value.convert(&mut false).value; println!("{}", converted.to_bits());
    }
    for integer in [0, 1, -1, 2049, -2049, 65520, 16777217, 9007199254740993, i128::MAX, i128::MIN] {
        println!("{}", F::from_i128(integer).value.to_bits());
    }
}
fn nan_choices<F: Float + FloatConvert<T>, T: Float>() {
    let inputs = corpus::<F>();
    let preferred = T::qnan(Some(0));
    let mut quieted = Vec::new();
    let mut signaling = Vec::new();
    for &input in &inputs {
        if input.is_nan() {
            let converted: T = input.convert(&mut false).value;
            quieted.push(converted);
        }
        if input.is_signaling() {
            let converted: T = input.convert(&mut false).value;
            let converted = T::from_bits(converted.to_bits() & !(1 << (T::PRECISION-2)));
            if converted.is_nan() { signaling.push(converted); }
        }
    }
    let values: Vec<_> = std::iter::once(preferred).chain(quieted).chain(signaling).collect();
    println!("{}", values.len()*2);
    for value in values { println!("{}", value.to_bits()); println!("{}", (-value).to_bits()); }
    println!("1"); println!("{}", T::NAN.to_bits());
}
fn nan_targets<F: Float + FloatConvert<Half> + FloatConvert<Single> + FloatConvert<Double> + FloatConvert<Quad>>() {
    nan_choices::<F, Half>(); nan_choices::<F, Single>(); nan_choices::<F, Double>(); nan_choices::<F, Quad>();
}
fn main() {
    run::<Half>(); run::<Single>(); run::<Double>(); run::<Quad>();
    nan_targets::<Half>(); nan_targets::<Single>(); nan_targets::<Double>(); nan_targets::<Quad>();
}
