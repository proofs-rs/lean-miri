// Use -Zmir-opt-level=0: the caller never materializes [Novel; 2].
#[derive(Clone, Copy)]
struct Novel(u32);

#[inline(never)]
fn local_array<T: Copy>(value: T) -> T {
    let pair = [value, value];
    let _copied = pair;
    value
}

fn main() {
    assert_eq!(local_array(Novel(73)).0, 73);
}
