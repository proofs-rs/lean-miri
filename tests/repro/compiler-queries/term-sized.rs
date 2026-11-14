#![no_std]
pub struct Tail<T: ?Sized> { pub head: u8, pub tail: T }
pub struct PointerTail<T: ?Sized> { pub pointer: *const T }
pub fn term_sized_root(value: &Tail<u8>, pointer: PointerTail<u8>) -> u8 {
    if pointer.pointer.is_null() { 0 } else { value.tail }
}
