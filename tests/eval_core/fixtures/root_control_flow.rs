#[inline(never)]
fn identity<T>(value: T) -> T {
    value
}

#[inline(never)]
fn loop_body() -> u32 {
    let promoted: &'static u32 = &7u32;
    let mut value = identity(*promoted);
    let mut index = 0u32;
    while index < 2 {
        value = identity(value + 1);
        index += 1;
    }
    value
}

pub fn root_control_flow() -> u32 {
    loop_body()
}
