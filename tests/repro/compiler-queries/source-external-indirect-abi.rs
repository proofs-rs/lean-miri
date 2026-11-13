#![no_std]
extern crate foreign_abi_dep;
pub fn root(){
 core::hint::black_box(foreign_abi_dep::identity([1u8;8]));
 core::hint::black_box(foreign_abi_dep::identity([1u8;9]));
 core::hint::black_box(foreign_abi_dep::identity((1u8,2u8,3u8,4u8,5u8,6u8,7u8,8u8,9u8)));
 core::hint::black_box(foreign_abi_dep::identity((1u64,2u64)));
 core::hint::black_box(foreign_abi_dep::identity((1u128,2u128)));
 core::hint::black_box(foreign_abi_dep::accept_pair((1,2)));
 core::hint::black_box(foreign_abi_dep::identity((core::ptr::null::<u8>(),1u64)));
}
