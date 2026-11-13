pub trait Scalar { type Item; }
impl Scalar for u8 { type Item=u32; }
pub mod left {
    #[repr(C)] pub struct Record<T:super::Scalar> {pub value:T::Item}
}
pub mod right {
    #[repr(C)] pub struct Record {pub value:u32}
}
pub fn source_alias(_:left::Record<u8>,_:right::Record) {}
