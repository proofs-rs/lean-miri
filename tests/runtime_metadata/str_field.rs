pub fn str_field(value: &str) -> *const u8 {
    value.as_ptr()
}
