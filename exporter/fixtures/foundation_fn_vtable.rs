#![crate_type = "lib"]

// Same principal/Output/auto-trait shape as std::rt::lang_start_internal;
// a static reference avoids introducing an unrelated late-bound input region.
pub fn boundary(
    main: &'static (dyn Fn() -> i32 + Sync + std::panic::RefUnwindSafe),
) -> &'static (dyn Fn() -> i32 + Sync + std::panic::RefUnwindSafe) { main }

fn concrete() -> i32 { 0 }
// Independent schema12 compiler oracle forces a real concrete Fn vtable.
// Foundation currently rejects its promoted pointer/vtable allocation source.
pub fn concrete_vtable() -> &'static (dyn Fn() -> i32 + Sync + std::panic::RefUnwindSafe) {
    &(concrete as fn() -> i32)
}
