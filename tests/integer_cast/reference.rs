#![feature(core_intrinsics)]
#![allow(internal_features)]

macro_rules! emit_int_casts {
    ($source:literal, $raw:expr, $value:expr) => {{
        let value = $value;
        let results = [
            (value as i8 as u8 as u128).to_string(), (value as u8 as u128).to_string(),
            (value as i16 as u16 as u128).to_string(), (value as u16 as u128).to_string(),
            (value as i32 as u32 as u128).to_string(), (value as u32 as u128).to_string(),
            (value as i64 as u64 as u128).to_string(), (value as u64 as u128).to_string(),
            (value as i128 as u128).to_string(), (value as u128).to_string(),
            (value as isize as usize as u128).to_string(), (value as usize as u128).to_string(),
        ];
        println!("C|{}|{}|{}", $source, $raw, results.join("|"));
    }};
}

macro_rules! emit_numeric {
    ($ty_name:literal, $ty:ty, $value:expr) => {{
        let value: $ty = $value;
        let raw = value as u128;
        let (cttz_nonzero, ctlz_nonzero) = if value == 0 {
            ("-".to_owned(), "-".to_owned())
        } else {
            (
                unsafe { core::intrinsics::cttz_nonzero(value) }.to_string(),
                unsafe { core::intrinsics::ctlz_nonzero(value) }.to_string(),
            )
        };
        let results = [
            core::intrinsics::ctpop(value).to_string(),
            core::intrinsics::cttz(value).to_string(),
            cttz_nonzero,
            core::intrinsics::ctlz(value).to_string(),
            ctlz_nonzero,
            (core::intrinsics::bswap(value) as u128).to_string(),
            (core::intrinsics::bitreverse(value) as u128).to_string(),
        ];
        println!("N|{}|{}|{}", $ty_name, raw, results.join("|"));
    }};
}

macro_rules! emit_saturating {
    ($ty_name:literal, $ty:ty, $raw_ty:ty, $left:expr, $right:expr) => {{
        let left: $ty = $left;
        let right: $ty = $right;
        println!(
            "S|{}|{}|{}|{}|{}",
            $ty_name,
            left as $raw_ty as u128,
            right as $raw_ty as u128,
            core::intrinsics::saturating_add(left, right) as $raw_ty as u128,
            core::intrinsics::saturating_sub(left, right) as $raw_ty as u128,
        );
    }};
}

macro_rules! emit_exact_div {
    ($ty_name:literal, $ty:ty, $raw_ty:ty, $left:expr, $right:expr) => {{
        let left: $ty = $left;
        let right: $ty = $right;
        println!(
            "D|{}|{}|{}|{}",
            $ty_name,
            left as $raw_ty as u128,
            right as $raw_ty as u128,
            unsafe { core::intrinsics::exact_div(left, right) } as $raw_ty as u128,
        );
    }};
}

fn main() {
    assert_eq!(core::mem::size_of::<usize>(), 8);

    for value in [-128i8, -1, 0, 127] {
        emit_int_casts!("i8", value as u8 as u128, value);
    }
    for value in [0u8, 1, 127, 128, u8::MAX] {
        emit_int_casts!("u8", value as u128, value);
        println!("C|u8|{}|char|{}", value, value as char as u32);
    }
    for value in [i16::MIN, -1, 0, i16::MAX] {
        emit_int_casts!("i16", value as u16 as u128, value);
    }
    for value in [0u16, 1, 1 << 15, u16::MAX] {
        emit_int_casts!("u16", value as u128, value);
    }
    for value in [i32::MIN, -1, 0, i32::MAX] {
        emit_int_casts!("i32", value as u32 as u128, value);
    }
    for value in [0u32, 1, 1 << 31, u32::MAX] {
        emit_int_casts!("u32", value as u128, value);
    }
    for value in [i64::MIN, -1, 0, i64::MAX] {
        emit_int_casts!("i64", value as u64 as u128, value);
    }
    for value in [0u64, 1, 1 << 63, u64::MAX] {
        emit_int_casts!("u64", value as u128, value);
    }
    for value in [i128::MIN, -1, 0, i128::MAX] {
        emit_int_casts!("i128", value as u128, value);
    }
    for value in [0u128, 1, 1u128 << 127, u128::MAX] {
        emit_int_casts!("u128", value, value);
    }
    for value in [isize::MIN, -1, 0, isize::MAX] {
        emit_int_casts!("isize", value as usize as u128, value);
    }
    for value in [0usize, 1, 1usize << 63, usize::MAX] {
        emit_int_casts!("usize", value as u128, value);
    }
    for value in [false, true] {
        emit_int_casts!("bool", value as u8 as u128, value);
    }
    for value in ['\0', 'A', '\u{e000}', '\u{10ffff}'] {
        emit_int_casts!("char", value as u32 as u128, value);
    }

    emit_saturating!("i8", i8, u8, i8::MAX, 1);
    emit_saturating!("i8", i8, u8, i8::MIN, -1);
    emit_saturating!("u8", u8, u8, u8::MAX, 1);
    emit_saturating!("u8", u8, u8, 0, 1);
    emit_saturating!("i128", i128, u128, i128::MAX, 1);
    emit_saturating!("i128", i128, u128, i128::MIN, -1);
    emit_saturating!("u128", u128, u128, u128::MAX, 1);
    emit_saturating!("u128", u128, u128, 0, 1);

    emit_exact_div!("i8", i8, u8, -6, 2);
    emit_exact_div!("u8", u8, u8, 18, 3);
    emit_exact_div!("i128", i128, u128, i128::MIN, 1);
    emit_exact_div!("u128", u128, u128, u128::MAX, 3);

    emit_numeric!("u8", u8, 0);
    emit_numeric!("u8", u8, 1);
    emit_numeric!("u8", u8, 0x80);
    emit_numeric!("u8", u8, 0xa5);
    emit_numeric!("u8", u8, u8::MAX);
    emit_numeric!("u16", u16, 0);
    emit_numeric!("u16", u16, 1);
    emit_numeric!("u16", u16, 0x8000);
    emit_numeric!("u16", u16, 0xa55a);
    emit_numeric!("u16", u16, u16::MAX);
    emit_numeric!("u32", u32, 0);
    emit_numeric!("u32", u32, 1);
    emit_numeric!("u32", u32, 0x8000_0000);
    emit_numeric!("u32", u32, 0xa55a_a55a);
    emit_numeric!("u32", u32, u32::MAX);
    emit_numeric!("u64", u64, 0);
    emit_numeric!("u64", u64, 1);
    emit_numeric!("u64", u64, 0x8000_0000_0000_0000);
    emit_numeric!("u64", u64, 0xa55a_a55a_a55a_a55a);
    emit_numeric!("u64", u64, u64::MAX);
    emit_numeric!("u128", u128, 0);
    emit_numeric!("u128", u128, 1);
    emit_numeric!("u128", u128, 1u128 << 127);
    emit_numeric!("u128", u128, 0xa55a_a55a_a55a_a55a_a55a_a55a_a55a_a55a);
    emit_numeric!("u128", u128, u128::MAX);
    emit_numeric!("i8", i8, 0);
    emit_numeric!("i8", i8, 1);
    emit_numeric!("i8", i8, i8::MIN);
    emit_numeric!("i8", i8, -91);
    emit_numeric!("i8", i8, -1);
    emit_numeric!("i8", i8, i8::MAX);
    emit_numeric!("i128", i128, 0);
    emit_numeric!("i128", i128, 1);
    emit_numeric!("i128", i128, i128::MIN);
    emit_numeric!("i128", i128, -1);
    emit_numeric!("i128", i128, i128::MAX);
}
