use rustc_apfloat::{Float,Round};
use rustc_apfloat::ieee::{Half,Single,Double,Quad};
fn corpus<F:Float>()->Vec<F>{
 let frac=F::PRECISION-1;let sign=1u128<<(F::BITS-1);let inf=((1u128<<(F::BITS-frac-1))-1)<<frac;let one=((1u128<<((F::BITS-frac-1)-1))-1)<<frac;
 [0,sign,1,sign+1,(1<<frac)-1,1<<frac,one-1,one,one+1,one+(1<<(frac-1)),sign+one,sign+one+(1<<(frac-1)),inf-1,inf,sign+inf,inf+1,inf+(1<<(frac-1))].into_iter().map(F::from_bits).collect()
}
fn output<F:Float>(x:F){println!("{}",if x.is_nan(){F::NAN}else{x}.to_bits())}
fn run<F:Float>(){
 let values=corpus::<F>();
 for &a in &values{
  for mode in [Round::TowardNegative,Round::TowardPositive,Round::TowardZero,Round::NearestTiesToAway,Round::NearestTiesToEven]{output(a.round_to_integral(mode).value)}
  for &b in &values{
   for right_equal in [false,true]{
    output(a.minimum(b));output(a.maximum(b));
    output(if a==b {if right_equal{b}else{a}}else{a.min(b)});
    output(if a==b {if right_equal{b}else{a}}else{a.max(b)});
   }
   for &c in &values{output(a.mul_add(b,c).value)}
  }
 }
}
fn main(){run::<Half>();run::<Single>();run::<Double>();run::<Quad>();}
