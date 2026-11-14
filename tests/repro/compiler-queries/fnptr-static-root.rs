#[inline(never)] fn id<T>(value: T) -> T { value }
static VALUE: u32 = 43;
fn main() { let pointer: fn(u8) -> u8 = id::<u8>; assert_eq!(id(pointer)(53), 53); assert_eq!(VALUE, 43); }
