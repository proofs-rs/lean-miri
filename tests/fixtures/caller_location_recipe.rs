use std::panic::Location;

#[track_caller]
fn tracked() -> &'static Location<'static> {
    Location::caller()
}

macro_rules! location {
    () => { (Location::caller(), line!(), column!()) };
}

fn main() {
    let direct = tracked();
    let expected_line = line!() - 1;
    assert_eq!(direct.file(), file!());
    assert_eq!(direct.line(), expected_line);
    assert_eq!(direct.column(), 18);
    let (from_macro, expected_line, expected_column) = location!();
    assert_eq!(from_macro.file(), file!());
    assert_eq!(from_macro.line(), expected_line);
    assert_eq!(from_macro.column(), expected_column);
    let mut previous = None;
    for _ in 0..2 {
        let current = tracked();
        if let Some(previous) = previous {
            assert!(!std::ptr::eq(previous, current));
        }
        previous = Some(current);
    }
}
