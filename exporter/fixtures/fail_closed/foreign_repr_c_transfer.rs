#[repr(C)]
pub struct CallerType { pub field: i32 }

mod implementation {
    #[repr(C)]
    pub struct CalleeType { pub field: i32 }

    #[unsafe(no_mangle)]
    pub extern "C" fn foreign_repr_c(value: CalleeType) -> i32 { value.field }
}

pub fn identity(value: i32) -> i32 {
    unsafe extern "C" { fn foreign_repr_c(value: CallerType) -> i32; }
    unsafe { foreign_repr_c(CallerType { field: value }) }
}

fn main() { assert_eq!(identity(17), 17); }
