use std::any::Any;
pub fn result_layout(x: Result<isize, Box<dyn Any + Send>>) -> Result<isize, Box<dyn Any + Send>> { x }
