#![feature(core_io)]
#![feature(core_io_internals)]
#![no_std]

pub fn write_all_eof() -> core::io::Error {
    core::io::Error::WRITE_ALL_EOF
}
