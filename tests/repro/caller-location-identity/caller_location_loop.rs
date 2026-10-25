use std::panic::Location;

fn main() {
    let mut first: Option<*const Location<'static>> = None;
    for _ in 0..2 {
        // The same MIR source span executes twice. Observe allocation identity.
        let now = Location::caller() as *const Location<'static>;
        match first {
            None => first = Some(now),
            Some(previous) => println!("same={}", std::ptr::eq(previous, now)),
        }
    }
}
