fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let caught = std::panic::catch_unwind(|| panic!("intentional caught panic"));
    assert!(caught.is_err());
    drop(caught);
}
