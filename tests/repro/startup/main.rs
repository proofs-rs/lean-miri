fn main() {
    let value = [2_u32, 3_u32].into_iter().sum::<u32>();
    assert_eq!(value, 5);
}
