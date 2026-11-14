#![no_std]

pub struct Generic<T> { pub values: [T; 3], pub flag: bool }
pub struct Novel(pub u32);

pub fn world_layout_material(x: Generic<u8>, n: Novel) -> (Generic<u8>, Novel) { (x,n) }

pub fn world_layout_oracle<'a>(x: (Generic<Novel>, [Novel; 3], *const Generic<Novel>,
    &'a Generic<Novel>, &'a [Novel]))
    -> (Generic<Novel>, [Novel; 3], *const Generic<Novel>, &'a Generic<Novel>, &'a [Novel]) { x }
