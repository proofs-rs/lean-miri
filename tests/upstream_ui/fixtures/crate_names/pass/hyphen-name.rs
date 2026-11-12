struct Marker;
fn main() {
    assert_eq!(std::any::type_name::<Marker>(), "hyphen_name::Marker");
}
