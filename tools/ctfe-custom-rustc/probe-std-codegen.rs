fn main() {
    let values = vec![1_u32, 2, 3];
    assert_eq!(values.iter().copied().sum::<u32>(), 6);
    println!("PASS matching stage1 std Vec/iterator/codegen execution");
}
