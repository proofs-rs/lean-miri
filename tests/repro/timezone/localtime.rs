#![no_std]
#![no_main]

extern crate libc;

// Linux x86_64 and pinned Miri's chrono localtime_r semantics, not host libc.
// Every call changes guest TZ; no result depends on the host process's TZ.
unsafe fn check(seconds: i64, expected: [i32; 9], offset: i64, zone: &[u8]) -> bool {
    let mut result = core::mem::MaybeUninit::<libc::tm>::uninit();
    let returned = unsafe { libc::localtime_r(&seconds, result.as_mut_ptr()) };
    if returned != result.as_mut_ptr() { return false; }
    let result = unsafe { result.assume_init() };
    let fields = [result.tm_sec, result.tm_min, result.tm_hour, result.tm_mday,
        result.tm_mon, result.tm_year, result.tm_wday, result.tm_yday, result.tm_isdst];
    if fields != expected || result.tm_gmtoff != offset { return false; }
    for (index, byte) in zone.iter().enumerate() {
        if unsafe { *result.tm_zone.add(index) } as u8 != *byte { return false; }
    }
    true
}

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    unsafe {
        if libc::unsetenv(c"TZ".as_ptr()) != 0 { return 1; }
        if !check(0, [0,0,0,1,0,70,4,0,-1], 0, b"+00\0") { return 2; }
        if libc::setenv(c"TZ".as_ptr(), c"UTC".as_ptr(), 1) != 0 { return 3; }
        if !check(-1, [59,59,23,31,11,69,3,364,-1], 0, b"+00\0") { return 4; }
        if !check(951782400, [0,0,0,29,1,100,2,59,-1], 0, b"+00\0") { return 5; }
        if libc::setenv(c"TZ".as_ptr(), c"not/a/timezone".as_ptr(), 1) != 0 { return 6; }
        if !check(0, [0,0,0,1,0,70,4,0,-1], 0, b"+00\0") { return 7; }
        if libc::setenv(c"TZ".as_ptr(), b"\xff\0".as_ptr().cast(), 1) != 0 { return 8; }
        if !check(0, [0,0,0,1,0,70,4,0,-1], 0, b"+00\0") { return 9; }
        if libc::setenv(c"TZ".as_ptr(), c"America/New_York".as_ptr(), 1) != 0 { return 10; }
        if !check(1710053999, [59,59,1,10,2,124,0,69,-1], -18000, b"-05\0") { return 11; }
        if !check(1710054000, [0,0,3,10,2,124,0,69,-1], -14400, b"-04\0") { return 12; }
        if libc::setenv(c"TZ".as_ptr(), c"Asia/Kathmandu".as_ptr(), 1) != 0 { return 13; }
        if !check(1710054000, [0,45,12,10,2,124,0,69,-1], 20700, b"+0545\0") { return 14; }
    }
    0
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
