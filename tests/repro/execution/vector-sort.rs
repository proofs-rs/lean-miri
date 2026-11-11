fn main() {
    let mut values = Vec::with_capacity(16);
    for i in 0..16_u64 { values.push((i * 37) % 101); }
    values.sort_unstable();
    let mut checksum = 0_u64;
    for (i, value) in values.iter().enumerate() { checksum += (i as u64 + 1) * value; }
    assert_eq!(checksum, 8105);
}
