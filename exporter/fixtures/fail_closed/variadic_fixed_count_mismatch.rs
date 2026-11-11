unsafe extern "C" fn callee(_: i32, _: ...) {}

pub fn root() {
    unsafe {
        let pointer = callee as *const ();
        let caller = core::mem::transmute::<_, unsafe extern "C" fn(...)>(pointer);
        caller(1i32);
    }
}
