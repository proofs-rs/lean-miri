#![crate_name = "source_attribute"]
struct Marker;
fn main() {
    assert_eq!(std::any::type_name::<Marker>(), "source_attribute::Marker");
}
