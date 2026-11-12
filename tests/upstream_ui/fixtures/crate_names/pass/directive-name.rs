//@compile-flags: --crate-name source_flag_override
struct Marker;
fn main() {
    assert_eq!(std::any::type_name::<Marker>(), "source_flag_override::Marker");
}
