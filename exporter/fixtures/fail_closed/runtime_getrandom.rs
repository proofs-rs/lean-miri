#![feature(linkage)]
unsafe extern "C" {
    #[linkage = "extern_weak"]
    static getrandom: Option<unsafe extern "C" fn(*mut u8, usize, u32) -> isize>;
}
fn main() {
    let mut bytes = [0u8; 4];
    let function = unsafe { getrandom }.expect("pinned Linux Miri supplies getrandom");
    assert_eq!(unsafe { function(bytes.as_mut_ptr(), bytes.len(), 0) }, 4);
}
