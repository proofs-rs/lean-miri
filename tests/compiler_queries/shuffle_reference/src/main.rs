use rand::{RngCore,SeedableRng};
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
}
