#![no_std]
#![no_main]

#[repr(C)]
struct Header<T: ?Sized> {
    tag: u8,
    tail: T,
}

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let values: [u16; 3] = [0x1234, 0x5678, 0x9abc];
    let array_ref: &[u16; 3] = &values;
    let slice_ref: &[u16] = array_ref;
    if slice_ref.len() != 3
        || slice_ref[0] != 0x1234
        || slice_ref[1] != 0x5678
        || slice_ref[2] != 0x9abc
        || core::mem::size_of_val(slice_ref) != 6
        || core::mem::align_of_val(slice_ref) != 2
    {
        return 1;
    }

    let header = Header {
        tag: 0xa5,
        tail: [0x1111u16, 0x2222, 0x3333],
    };
    let sized_ref: &Header<[u16; 3]> = &header;
    let wide_ref: &Header<[u16]> = sized_ref;
    if wide_ref.tag != 0xa5
        || wide_ref.tail.len() != 3
        || wide_ref.tail[0] != 0x1111
        || wide_ref.tail[1] != 0x2222
        || wide_ref.tail[2] != 0x3333
        || core::mem::size_of_val(wide_ref) != 8
        || core::mem::align_of_val(wide_ref) != 2
    {
        return 2;
    }
    0
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
