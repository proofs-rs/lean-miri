use std::arch::x86_64::*;
fn main() {
    unsafe {
        let a = _mm512_set1_epi16(255);
        let zero = _mm512_setzero_si512();
        let result: [u8; 64] = std::mem::transmute(_mm512_packus_epi16(a, zero));
        for index in 0..64 {
            assert!(result[index] == if index % 16 < 8 { 255 } else { 0 });
        }
    }
}
