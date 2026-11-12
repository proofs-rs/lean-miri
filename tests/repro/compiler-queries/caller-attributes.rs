#[inline(never)]
#[track_caller]
pub fn tracked(input: u32) -> u32 { std::hint::black_box(input) + 1 }

#[inline(never)]
pub fn untracked(input: u32) -> u32 { std::hint::black_box(input) + 2 }

#[inline(never)]
pub fn caller_attributes(input: u32) -> u32 { untracked(tracked(input)) }
