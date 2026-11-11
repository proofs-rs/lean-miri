// Concrete async return values have a layout in the runtime Codegen typing
// environment even though their layout is intentionally TooGeneric during
// PostAnalysis. The constructed future is dropped before polling its coroutine body.
pub async fn make_future() -> u32 {
    7
}

pub fn root() {
    core::mem::drop(make_future());
}
