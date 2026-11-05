#![no_std]

use core::panic::Location;

#[track_caller]
fn tracked() -> &'static Location<'static> {
    Location::caller()
}

macro_rules! location {
    () => { Location::caller() };
}

pub fn root() -> (&'static Location<'static>, &'static Location<'static>) {
    (tracked(), location!())
}
