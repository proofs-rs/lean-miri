//! A minimal caller shim around the pinned rustc_abi source.
//!
//! WrappingRange is compiled directly from the pinned upstream file below.
//! The Size and Align bodies used here are source excerpts with only the
//! rustc-specific data-layout trait reduced to the small interface needed by
//! these methods.

use std::ops::{Add, Mul, Sub};

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Debug)]
struct Size { raw: u64 }

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
struct Align { pow2: u8 }

struct TargetDataLayout { pointer_bits: u64 }

impl TargetDataLayout {
    fn obj_size_bound(&self) -> u64 {
        match self.pointer_bits {
            16 => 1 << 15,
            32 => 1 << 31,
            64 => 1 << 61,
            bits => panic!("obj_size_bound: unknown pointer bit size {bits}"),
        }
    }
}

trait HasDataLayout { fn data_layout(&self) -> &TargetDataLayout; }
impl HasDataLayout for TargetDataLayout {
    fn data_layout(&self) -> &TargetDataLayout { self }
}

impl Size {
    fn from_bits(bits: u64) -> Size { Size { raw: bits.div_ceil(8) } }
    fn from_bytes(bytes: u64) -> Size { Size { raw: bytes } }
    fn bytes(self) -> u64 { self.raw }

    fn bits(self) -> u64 {
        self.bytes().checked_mul(8).unwrap_or_else(|| {
            panic!("Size::bits: {} bytes in bits doesn't fit in u64", self.bytes())
        })
    }

    fn align_to(self, align: Align) -> Size {
        let mask = align.bytes() - 1;
        Size::from_bytes((self.bytes() + mask) & !mask)
    }

    fn checked_add<C: HasDataLayout>(self, offset: Size, cx: &C) -> Option<Size> {
        let dl = cx.data_layout();
        let bytes = self.bytes().checked_add(offset.bytes())?;
        if bytes < dl.obj_size_bound() { Some(Size::from_bytes(bytes)) } else { None }
    }

    fn checked_mul<C: HasDataLayout>(self, count: u64, cx: &C) -> Option<Size> {
        let dl = cx.data_layout();
        let bytes = self.bytes().checked_mul(count)?;
        if bytes < dl.obj_size_bound() { Some(Size::from_bytes(bytes)) } else { None }
    }

    fn sign_extend(self, value: u128) -> i128 {
        let size = self.bits();
        if size == 0 { return 0; }
        let shift = 128 - size;
        ((value << shift) as i128) >> shift
    }

    fn truncate(self, value: u128) -> u128 {
        let size = self.bits();
        if size == 0 { return 0; }
        let shift = 128 - size;
        (value << shift) >> shift
    }

    fn unsigned_int_max(&self) -> u128 { u128::MAX >> (128 - self.bits()) }
}

impl Add for Size {
    type Output = Size;
    fn add(self, other: Size) -> Size {
        Size::from_bytes(self.bytes().checked_add(other.bytes()).unwrap_or_else(|| {
            panic!("Size::add: {} + {} doesn't fit in u64", self.bytes(), other.bytes())
        }))
    }
}

impl Sub for Size {
    type Output = Size;
    fn sub(self, other: Size) -> Size {
        Size::from_bytes(self.bytes().checked_sub(other.bytes()).unwrap_or_else(|| {
            panic!("Size::sub: {} - {} would result in negative size", self.bytes(), other.bytes())
        }))
    }
}

impl Mul<u64> for Size {
    type Output = Size;
    fn mul(self, count: u64) -> Size {
        match self.bytes().checked_mul(count) {
            Some(bytes) => Size::from_bytes(bytes),
            None => panic!("Size::mul: {} * {} doesn't fit in u64", self.bytes(), count),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum AlignFromBytesError { NotPowerOfTwo(u64), TooLarge(u64) }

impl Align {
    const ONE: Align = Align { pow2: 0 };
    const EIGHT: Align = Align { pow2: 3 };
    const MAX: Align = Align { pow2: 29 };

    fn from_bits(bits: u64) -> Result<Align, AlignFromBytesError> {
        Align::from_bytes(Size::from_bits(bits).bytes())
    }

    fn from_bytes(align: u64) -> Result<Align, AlignFromBytesError> {
        if align == 0 { return Ok(Align::ONE); }
        let tz = align.trailing_zeros();
        if align != (1 << tz) { return Err(AlignFromBytesError::NotPowerOfTwo(align)); }
        let pow2 = tz as u8;
        if pow2 > Self::MAX.pow2 { return Err(AlignFromBytesError::TooLarge(align)); }
        Ok(Align { pow2 })
    }

    fn bytes(self) -> u64 { 1 << self.pow2 }

    fn max_aligned_factor(size: Size) -> Align {
        Align { pow2: size.bytes().trailing_zeros() as u8 }
    }

    fn restrict_for_offset(self, size: Size) -> Align {
        Align { pow2: self.pow2.min(Self::max_aligned_factor(size).pow2) }
    }
}

#[path = "../../upstream/rustc-source/compiler/rustc_abi/src/wrapping_range.rs"]
mod wrapping_range;
use wrapping_range::WrappingRange;

fn main() {
    let layout16 = TargetDataLayout { pointer_bits: 16 };
    let align8 = Align::EIGHT;
    let values = [1_u128, 254];
    let wrap = WrappingRange::smallest_range_containing(values, Size::from_bytes(1)).unwrap();
    let full = WrappingRange { start: 128, end: 127 };

    println!("from_bits_9={}", Size::from_bits(9).bytes());
    println!("bits_boundary={}", Size::from_bytes(u64::MAX / 8).bits());
    println!("bits_overflow={}", std::panic::catch_unwind(|| Size::from_bytes(u64::MAX / 8 + 1).bits()).is_err());
    println!("unsigned_max_zero={}", std::panic::catch_unwind(|| Size::from_bytes(0).unsigned_int_max()).is_err());
    println!("add_overflow={}", std::panic::catch_unwind(|| Size::from_bytes(u64::MAX) + Size::from_bytes(1)).is_err());
    println!("sub_overflow={}", std::panic::catch_unwind(|| Size::from_bytes(0) - Size::from_bytes(1)).is_err());
    println!("mul_overflow={}", std::panic::catch_unwind(|| Size::from_bytes(u64::MAX) * 2).is_err());
    println!("truncate8={}", Size::from_bytes(1).truncate(511));
    println!("sign8={}", Size::from_bytes(1).sign_extend(255));
    println!("sign128={}", Size::from_bytes(16).sign_extend(1_u128 << 127));
    println!("obj16_below={}", Size::from_bytes(32767).checked_add(Size::from_bytes(0), &layout16).unwrap().bytes());
    println!("obj16_at={}", Size::from_bytes(32767).checked_add(Size::from_bytes(1), &layout16).is_none());
    println!("mul16_below={}", Size::from_bytes(32767).checked_mul(1, &layout16).unwrap().bytes());
    println!("mul16_at={}", Size::from_bytes(16384).checked_mul(2, &layout16).is_none());
    println!("align_ceil={}", Align::from_bits(9).unwrap().bytes());
    println!("align_max={}", Align::from_bytes(1 << 29).unwrap().bytes());
    println!("align_too_large={}", matches!(Align::from_bytes(1 << 30), Err(AlignFromBytesError::TooLarge(_))));
    println!("align_overflow={}", std::panic::catch_unwind(|| Size::from_bytes(u64::MAX).align_to(align8)).is_err());
    println!("zero_factor_restrict={}", Align::EIGHT.restrict_for_offset(Size::from_bytes(0)).bytes());
    println!("zero_factor_bytes_overflow={}", std::panic::catch_unwind(|| Align::max_aligned_factor(Size::from_bytes(0)).bytes()).is_err());
    println!("range_contains={}", WrappingRange { start: 254, end: 2 }.contains(1));
    println!("range_full={}", full.is_full_for(Size::from_bytes(1)));
    println!("range_unsigned_wrap={}", WrappingRange { start: 254, end: 2 }.no_unsigned_wraparound(Size::from_bytes(1)).unwrap());
    println!("range_signed_wrap={}", WrappingRange { start: 254, end: 2 }.no_signed_wraparound(Size::from_bytes(1)).unwrap());
    println!("smallest={}:{}", wrap.start, wrap.end);
}
