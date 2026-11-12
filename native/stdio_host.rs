#![feature(io_error_more, io_error_inprogress, io_error_input_output_error, io_error_too_many_open_files)]
// Built with pinned rustc 8144389c895da997dbdecaa635e41d6a50be6ffd.
// Guest streams use exactly one Write::write / Write::flush invocation.
use std::{fs::File, io::{self, Write}, os::fd::{FromRawFd, AsRawFd}, sync::Mutex};
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Result { status:u32, kind:u32, raw_present:u32, raw:i32, count:u64 }
impl Result {
 fn ok(count:u64)->Self { Self{status:0,kind:0,raw_present:0,raw:0,count} }
 fn invalid()->Self { Self{status:3,..Self::ok(0)} }
 fn error(e:io::Error)->Self {
  let kind=match e.kind() {
   io::ErrorKind::ArgumentListTooLong => 1,
   io::ErrorKind::AddrInUse => 2,
   io::ErrorKind::AddrNotAvailable => 3,
   io::ErrorKind::ResourceBusy => 4,
   io::ErrorKind::ConnectionAborted => 5,
   io::ErrorKind::ConnectionRefused => 6,
   io::ErrorKind::ConnectionReset => 7,
   io::ErrorKind::Deadlock => 8,
   io::ErrorKind::QuotaExceeded => 9,
   io::ErrorKind::AlreadyExists => 10,
   io::ErrorKind::FileTooLarge => 11,
   io::ErrorKind::HostUnreachable => 12,
   io::ErrorKind::Interrupted => 13,
   io::ErrorKind::InvalidInput => 14,
   io::ErrorKind::IsADirectory => 15,
   io::ErrorKind::FilesystemLoop => 16,
   io::ErrorKind::NotFound => 17,
   io::ErrorKind::OutOfMemory => 18,
   io::ErrorKind::StorageFull => 19,
   io::ErrorKind::TooManyLinks => 20,
   io::ErrorKind::InvalidFilename => 21,
   io::ErrorKind::NetworkDown => 22,
   io::ErrorKind::NetworkUnreachable => 23,
   io::ErrorKind::NotConnected => 24,
   io::ErrorKind::NotADirectory => 25,
   io::ErrorKind::DirectoryNotEmpty => 26,
   io::ErrorKind::BrokenPipe => 27,
   io::ErrorKind::ReadOnlyFilesystem => 28,
   io::ErrorKind::NotSeekable => 29,
   io::ErrorKind::StaleNetworkFileHandle => 30,
   io::ErrorKind::TimedOut => 31,
   io::ErrorKind::ExecutableFileBusy => 32,
   io::ErrorKind::CrossesDevices => 33,
   io::ErrorKind::InProgress => 34,
   io::ErrorKind::InputOutputError => 35,
   io::ErrorKind::PermissionDenied => 36,
   io::ErrorKind::WouldBlock => 37,
   io::ErrorKind::Unsupported => 38,
   io::ErrorKind::TooManyOpenFiles => 39,
   io::ErrorKind::Other => 40,
   _ => 0,
  };
  let raw=e.raw_os_error();
  Self{status:if kind==0 {2} else {1},kind,raw_present:u32::from(raw.is_some()),raw:raw.unwrap_or(0),count:0}
 }
}
fn guard(f:impl FnOnce()->Result)->Result { std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)).unwrap_or_else(|_|Result::invalid()) }
unsafe extern "C" { fn lean_miri_stdio_check_fd(fd:i32)->i32; }
// A once-only adopted descriptor is never guest-visible and is closed exactly once.
struct Control { adopted:bool, file:Option<File> }
static CONTROL:Mutex<Control>=Mutex::new(Control{adopted:false,file:None});
fn once(writer:&mut impl Write, bytes:&[u8])->Result {
 match writer.write(bytes){Ok(n) if n<=bytes.len()=>Result::ok(n as u64),Ok(_)=>Result::invalid(),Err(e)=>Result::error(e)}
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn lean_miri_stdio_rust_write(stream:u32, bytes:*const u8, len:usize)->Result { guard(|| {
 if bytes.is_null() || len > isize::MAX as usize {return Result::invalid()}
 // C borrows a live Lean ByteArray for this synchronous call only.
 let bytes=unsafe {std::slice::from_raw_parts(bytes,len)};
 match stream {0=>once(&mut io::stdout(),bytes),1=>once(&mut io::stderr(),bytes),_=>Result::invalid()}
}) }
#[unsafe(no_mangle)]
pub extern "C" fn lean_miri_stdio_rust_flush()->Result {guard(||match io::stdout().flush(){Ok(())=>Result::ok(0),Err(e)=>Result::error(e)})}
#[unsafe(no_mangle)]
pub extern "C" fn lean_miri_stdio_rust_adopt(fd:u32)->Result {guard(|| {
 let Ok(mut c)=CONTROL.lock() else {return Result::invalid()};
 if c.adopted || fd<3 || fd>i32::MAX as u32 {return Result::invalid()}
 if unsafe{lean_miri_stdio_check_fd(fd as i32)}!=0 {return Result::error(io::Error::last_os_error())}
 // Transfer the inherited child's descriptor, then duplicate privately. The
 // parent has its independent descriptor ownership and is unaffected.
 let original=unsafe{File::from_raw_fd(fd as i32)};
 let private=match original.try_clone(){Ok(f)=>f,Err(e)=>return Result::error(e)};
 if unsafe{lean_miri_stdio_check_fd(private.as_raw_fd())}!=0 {return Result::error(io::Error::last_os_error())}
 drop(original);
 c.adopted=true;c.file=Some(private);Result::ok(0)
})}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn lean_miri_stdio_rust_control(bytes:*const u8,len:usize)->Result {guard(|| {
 if bytes.is_null() || len > isize::MAX as usize {return Result::invalid()}
 let Ok(mut c)=CONTROL.lock() else {return Result::invalid()};
 let Some(file)=c.file.as_mut() else {return Result::invalid()};
 let bytes=unsafe{std::slice::from_raw_parts(bytes,len)};
 match file.write_all(bytes){Ok(())=>Result::ok(len as u64),Err(e)=>Result::error(e)}
})}
#[unsafe(no_mangle)]
pub extern "C" fn lean_miri_stdio_rust_close()->Result {guard(|| {
 let Ok(mut c)=CONTROL.lock() else {return Result::invalid()};
 let Some(file)=c.file.take() else {return Result::invalid()};
 drop(file);Result::ok(0)
})}

#[cfg(test)]
mod tests {
 use super::*;
 struct Fixture { calls:usize, result:io::Result<usize> }
 impl Write for Fixture {
  fn write(&mut self,_:&[u8])->io::Result<usize>{self.calls+=1;std::mem::replace(&mut self.result,Ok(999))}
  fn flush(&mut self)->io::Result<()>{panic!("guest write must not flush")}
 }
 #[test] fn exact_one_call_counts_and_errors(){
  for n in [0,1,3] {let mut w=Fixture{calls:0,result:Ok(n)};let r=once(&mut w,b"abc");assert_eq!((r.status,r.count,w.calls),(0,n as u64,1));}
  let mut w=Fixture{calls:0,result:Err(io::Error::from(io::ErrorKind::Interrupted))};let r=once(&mut w,b"abc");assert_eq!((r.status,r.kind,r.raw_present,w.calls),(1,13,0,1));
  let mut w=Fixture{calls:0,result:Ok(4)};assert_eq!(once(&mut w,b"abc").status,3);
 }
 #[test] fn oversized_slice_rejected_before_borrow(){
  let pointer=std::ptr::NonNull::<u8>::dangling().as_ptr();
  let len=isize::MAX as usize+1;
  assert_eq!(unsafe{lean_miri_stdio_rust_write(0,pointer,len)}.status,3);
  assert_eq!(unsafe{lean_miri_stdio_rust_control(pointer,len)}.status,3);
 }
 #[test] fn raw_and_unknown_kinds(){
  let r=Result::error(io::Error::from_raw_os_error(-123));assert_eq!((r.raw_present,r.raw),(1,-123));
  assert_eq!(Result::error(io::Error::from(io::ErrorKind::InvalidData)).status,2);
  assert_eq!(guard(||panic!("fixture panic")).status,3);
 }
}
