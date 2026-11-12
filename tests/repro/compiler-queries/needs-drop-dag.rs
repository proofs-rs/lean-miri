#![allow(dead_code)]
pub struct D0(pub u8);
pub struct D1(pub D0, pub D0);
pub struct D2(pub D1, pub D1);
pub struct D3(pub D2, pub D2);
pub struct D4(pub D3, pub D3);
pub struct D5(pub D4, pub D4);
pub struct D6(pub D5, pub D5);
pub struct D7(pub D6, pub D6);
pub struct D8(pub D7, pub D7);
pub struct D9(pub D8, pub D8);
pub struct D10(pub D9, pub D9);
pub struct D11(pub D10, pub D10);
pub struct D12(pub D11, pub D11);
pub struct D13(pub D12, pub D12);
pub struct D14(pub D13, pub D13);
pub struct D15(pub D14, pub D14);
pub struct D16(pub D15, pub D15);
pub struct D17(pub D16, pub D16);
pub struct D18(pub D17, pub D17);
pub struct D19(pub D18, pub D18);
pub struct D20(pub D19, pub D19);
pub struct D21(pub D20, pub D20);
pub struct D22(pub D21, pub D21);
pub struct D23(pub D22, pub D22);
pub struct D24(pub D23, pub D23);
pub struct D25(pub D24, pub D24);
pub struct D26(pub D25, pub D25);
pub struct D27(pub D26, pub D26);
pub struct D28(pub D27, pub D27);

// Twenty-nine material nodes represent over 2^28 transitive leaf paths.
// The argument is borrowed, so this test never allocates the large value.
#[inline(never)]
pub fn needs_drop_dag(input: &D28) -> *const () {
    input as *const D28 as *const ()
}
