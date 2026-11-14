#![no_std]
#![allow(dead_code)]
pub type One = for<'a> fn(&'a u8) -> &'a u8;
pub type Reversed = for<'a, 'b> fn(&'b u8, &'a u8) -> &'a u8;
pub type Nested = for<'a> fn(for<'b> fn(&'a u8, &'b u8) -> &'a u8);
pub type InnerFirst = for<'a> fn(for<'b> fn(&'b u8) -> &'b u8, &'a u8);
pub type Static = for<'a> fn(&'a u8, &'static u8) -> &'a u8;
pub type Unused = for<'unused, 'a> fn(&'a u8);
pub type Variadic = for<'a> unsafe extern "C" fn(&'a u8, ...) -> &'a u8;
pub type Tuple = for<'a, 'b> fn((&'a u8, *const &'b u16)) -> &'b u16;
pub type NestedReference = for<'a> fn(&'a for<'b> fn(&'b u16) -> &'b u16) -> &'a u8;
pub fn root(_a: One, _b: Reversed, _c: Nested, _d: InnerFirst, _e: Static,
    _f: Unused, _g: Variadic, _h: Tuple, _i: NestedReference) {}
