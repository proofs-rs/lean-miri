use rand::{Rng,RngCore,SeedableRng};
use rand::seq::SliceRandom;
use rand_xoshiro::Xoshiro128StarStar;
fn main() {
    for seed in [0,1,42,u64::MAX,0x123456789abcdef0] {
        for size in [0,1,2,3,4,7,12,16,37,100] {
            let mut rng=Xoshiro128StarStar::seed_from_u64(seed);
            let mut values=(0..size).collect::<Vec<usize>>();
            values.shuffle(&mut rng);
            println!("{} {}:{};next={}",seed,size,values.iter().map(usize::to_string).collect::<Vec<_>>().join(","),rng.next_u32());
        }
    }
    for seed in [0,1,42,u64::MAX,0x123456789abcdef0] {
        for bound in [1u32,2,3,65537,2147483649,u32::MAX] {
            let mut rng=Xoshiro128StarStar::seed_from_u64(seed);
            let value=rng.random_range(..bound);
            println!("u32 {} {}:{};next={}",seed,bound,value,rng.next_u32());
        }
        for bound in [1u64,2,3,4294967297,9223372036854775809,u64::MAX] {
            let mut rng=Xoshiro128StarStar::seed_from_u64(seed);
            let value=rng.random_range(..bound);
            println!("u64 {} {}:{};next={}",seed,bound,value,rng.next_u32());
        }
    }
}
