// VaList's higher-ranked intrinsic signatures retain the source regions in
// their Binder graph. Only the separate compiler-query view may erase them.
pub unsafe extern "C" fn root(mut arguments: ...) -> i32 {
    unsafe { arguments.next_arg() }
}
