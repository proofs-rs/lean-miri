#![no_std]
#![no_main]
trait Value {
    fn get(&self, add:u32)->u32;
    fn set(&mut self, value:u32);
}
struct Cell(u32);
impl Value for Cell {
    fn get(&self, add:u32)->u32 {self.0+add}
    fn set(&mut self, value:u32) {self.0=value;}
}
#[inline(never)]
fn through(value:&mut dyn Value)->isize {
    if value.get(4)!=11 {return 1;}
    value.set(9);
    if value.get(3)==12 {0} else {2}
}
#[unsafe(no_mangle)]
pub fn miri_start(_argc:isize,_argv:*const *const u8)->isize {
    let mut value=Cell(7);through(&mut value)
}
#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo)->! {loop{}}
