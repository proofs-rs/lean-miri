// Use -Zmir-opt-level=0 to retain the tuple and uninitialized ADT local.
#[derive(Clone, Copy)]
struct Novel(u32);
struct Wrapper<T>(T);

#[inline(never)]
fn local_types<T: Copy>(value: T) -> T {
    let pair = (value, value);
    let _copied = pair;
    let _reserved: Wrapper<T>;
    value
}

fn main() { assert_eq!(local_types(Novel(73)).0, 73); }
