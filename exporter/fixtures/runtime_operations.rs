struct BorrowOnly(u32);
struct OwnedDrop(u32);
static DROPS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
impl Drop for OwnedDrop {
    fn drop(&mut self) {
        assert_eq!(self.0, 7);
        DROPS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }
}
trait View { fn value(&self) -> u32; }
struct EmptyDyn(u32);
impl View for EmptyDyn { fn value(&self) -> u32 { self.0 } }
#[inline(never)]
fn borrowed(x: &BorrowOnly) -> u32 { x.0 }
#[inline(never)]
fn dynamic(x: Box<dyn View>) -> u32 { x.value() }
fn main() {
    assert_eq!(borrowed(&BorrowOnly(3)), 3);
    let owned = OwnedDrop(7);
    drop(owned);
    let boxed = Box::new(OwnedDrop(7));
    drop(boxed);
    assert_eq!(DROPS.load(std::sync::atomic::Ordering::Relaxed), 2);
    // A null vtable drop slot still needs the concrete &mut T constructor.
    assert_eq!(dynamic(Box::new(EmptyDyn(9))), 9);
}
