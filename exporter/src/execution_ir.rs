//! Entire source → checked typed execution IR → unchanged interpreter, in one
//! process. Only normal constructor factories cross this private C ABI. The
//! complete existing Lean decoder/lowerer/provider checks run in the producer;
//! no serialized heap, unsafe object cast or trusted readiness flag is used.
use crate::prepared_image::{Image, Row};
use std::ffi::{CStr, CString, c_char, c_int, c_void};
use std::path::PathBuf;
use std::ptr::NonNull;

type Raw = *mut c_void;
#[link(name = "dl")]
unsafe extern "C" {
    fn dlopen(path: *const c_char, flags: c_int) -> Raw;
    fn dlsym(handle: Raw, name: *const c_char) -> Raw;
    fn dlerror() -> *const c_char;
}

struct Backend {
    // Keep the code/runtime loaded until process exit; roots may reference its
    // module-owned immutable data even after the last public call.
    _library: Raw,
    finalize: unsafe extern "C" fn(),
    dec: unsafe extern "C" fn(Raw),
    array: unsafe extern "C" fn(usize) -> Raw,
    push: unsafe extern "C" fn(Raw, Raw) -> Raw,
    nat: unsafe extern "C" fn(u64) -> Raw,
    string: unsafe extern "C" fn(*const c_char, usize) -> Raw,
    pair: unsafe extern "C" fn(u64, u64) -> Raw,
    scalar: unsafe extern "C" fn(u8, Raw) -> Raw,
    natural: unsafe extern "C" fn(u64) -> Raw,
    row_array: unsafe extern "C" fn(Raw) -> Raw,
    row_object: unsafe extern "C" fn(Raw) -> Raw,
    image: unsafe extern "C" fn(Raw, Raw, u64) -> Raw,
    compile: unsafe extern "C" fn(Raw, Raw) -> Raw,
    run: unsafe extern "C" fn(Raw) -> c_int,
}

/// Every Object is produced by its matching typed Lean constructor/IO result.
/// Rust never inspects Lean object headers or changes a value's type.
struct Object<'a> {
    value: NonNull<c_void>,
    backend: &'a Backend,
}
impl Drop for Object<'_> {
    fn drop(&mut self) { unsafe { (self.backend.dec)(self.value.as_ptr()) } }
}
impl Object<'_> {
    fn transfer(self) -> Raw {
        let pointer = self.value.as_ptr();
        std::mem::forget(self);
        pointer
    }
}
impl Drop for Backend {
    fn drop(&mut self) { unsafe { (self.finalize)() } }
}

unsafe fn symbol(library: Raw, name: &'static CStr) -> Result<Raw, String> {
    let pointer = unsafe { dlsym(library, name.as_ptr()) };
    if pointer.is_null() {
        return Err(format!("execution IR library missing {}", name.to_string_lossy()));
    }
    Ok(pointer)
}

impl Backend {
    fn open() -> Result<Self, String> {
        let path = std::env::var_os("LEAN_MIRI_EXECUTION_IR_LIBRARY")
            .map(PathBuf::from).unwrap_or_else(|| PathBuf::from(concat!(
                env!("CARGO_MANIFEST_DIR"), "/../.lake/build/lib/libexecution_ir.so")));
        let path = CString::new(path.as_os_str().as_encoded_bytes())
            .map_err(|_| "execution IR library path contains NUL")?;
        let library = unsafe { dlopen(path.as_ptr(), 2 /* RTLD_NOW, local symbols */) };
        if library.is_null() {
            let error = unsafe { dlerror() };
            return Err(if error.is_null() { "cannot load execution IR library".into() }
                else { unsafe { CStr::from_ptr(error) }.to_string_lossy().into_owned() });
        }
        // Each cast is a function pointer for the fixed versioned C shim, not
        // a cast of input data. Missing/version-incompatible libraries fail.
        macro_rules! load {
            ($name:literal, $ty:ty) => {
                unsafe { std::mem::transmute::<Raw, $ty>(symbol(library,
                    CStr::from_bytes_with_nul(concat!("lean_miri_bridge_", $name, "\0").as_bytes()).unwrap())?) }
            };
        }
        let version = load!("version", unsafe extern "C" fn() -> u64);
        if unsafe { version() } != 2 { return Err("execution IR ABI version mismatch".into()); }
        let initialize = load!("initialize", unsafe extern "C" fn() -> c_int);
        let backend = Self {
            _library: library,
            finalize: load!("finalize", unsafe extern "C" fn()),
            dec: load!("dec", unsafe extern "C" fn(Raw)),
            array: load!("array", unsafe extern "C" fn(usize) -> Raw),
            push: load!("push", unsafe extern "C" fn(Raw, Raw) -> Raw),
            nat: load!("nat", unsafe extern "C" fn(u64) -> Raw),
            string: load!("string", unsafe extern "C" fn(*const c_char, usize) -> Raw),
            pair: load!("pair", unsafe extern "C" fn(u64, u64) -> Raw),
            scalar: load!("scalar", unsafe extern "C" fn(u8, Raw) -> Raw),
            natural: load!("natural", unsafe extern "C" fn(u64) -> Raw),
            row_array: load!("row_array", unsafe extern "C" fn(Raw) -> Raw),
            row_object: load!("row_object", unsafe extern "C" fn(Raw) -> Raw),
            image: load!("image", unsafe extern "C" fn(Raw, Raw, u64) -> Raw),
            compile: load!("compile", unsafe extern "C" fn(Raw, Raw) -> Raw),
            run: load!("run", unsafe extern "C" fn(Raw) -> c_int),
        };
        if unsafe { initialize() } != 0 {
            // Finalizing an uninitialized task manager is not allowed.
            std::mem::forget(backend);
            return Err("execution IR Lean initialization failed".into());
        }
        Ok(backend)
    }
    fn own(&self, value: Raw) -> Result<Object<'_>, String> {
        Ok(Object { value: NonNull::new(value).ok_or("execution IR constructor/compilation failed")?, backend: self })
    }
    fn string(&self, text: &str) -> Result<Object<'_>, String> {
        self.own(unsafe { (self.string)(text.as_ptr().cast(), text.len()) })
    }
    fn array(&self, capacity: usize) -> Result<Object<'_>, String> {
        self.own(unsafe { (self.array)(capacity) })
    }
    fn push<'a>(&'a self, array: Object<'a>, value: Object<'a>) -> Result<Object<'a>, String> {
        self.own(unsafe { (self.push)(array.transfer(), value.transfer()) })
    }
    fn strings<'a, 's>(&'a self, values: impl IntoIterator<Item = &'s str>) -> Result<Object<'a>, String> {
        let mut result = self.array(0)?;
        for value in values { result = self.push(result, self.string(value)?)?; }
        Ok(result)
    }
    fn source_image(&self, image: Image) -> Result<Object<'_>, String> {
        let fields = self.strings(image.fields.iter().map(String::as_str))?;
        let mut nodes = self.array(image.nodes.len())?;
        for row in image.nodes {
            let value = match row {
                Row::Empty(tag) => self.own(unsafe { (self.scalar)(tag, self.string("")?.transfer()) })?,
                Row::Leaf(3, ref value) if value.as_u64().is_some() => {
                    self.own(unsafe { (self.natural)(value.as_u64().expect("guarded numeric leaf")) })?
                }
                Row::Leaf(tag, value) => {
                    let text = if tag == 4 { value.as_str().ok_or("invalid source string row")?.to_owned() }
                        else { value.to_string() };
                    self.own(unsafe { (self.scalar)(tag, self.string(&text)?.transfer()) })?
                }
                Row::Array(ids) => {
                    let mut children = self.array(ids.len())?;
                    for id in ids {
                        children = self.push(children, self.own(unsafe { (self.nat)(id as u64) })?)?;
                    }
                    self.own(unsafe { (self.row_array)(children.transfer()) })?
                }
                Row::Object(pairs) => {
                    let mut fields = self.array(pairs.len())?;
                    for (field, child) in pairs {
                        fields = self.push(fields, self.own(unsafe { (self.pair)(field as u64, child as u64) })?)?;
                    }
                    self.own(unsafe { (self.row_object)(fields.transfer()) })?
                }
            };
            nodes = self.push(nodes, value)?;
        }
        self.own(unsafe { (self.image)(fields.transfer(), nodes.transfer(), image.root as u64) })
    }
}

pub(crate) fn run(image: Image) -> Result<(), String> {
    let args: Vec<String> = match std::env::var("LEAN_MIRI_EXECUTION_IR_ARGS_JSON") {
        Ok(raw) => serde_json::from_str(&raw).map_err(|error| format!("invalid execution IR args: {error}"))?,
        Err(std::env::VarError::NotPresent) => Vec::new(),
        Err(error) => return Err(error.to_string()),
    };
    let backend = Backend::open()?;
    let source = backend.source_image(image)?;
    let args = backend.strings(args.iter().map(String::as_str))?;
    // Complete checked compilation is counted in source-entry measurements.
    // The returned value owns all MIR, type, allocation and provider registries.
    let ir = backend.own(unsafe { (backend.compile)(source.transfer(), args.transfer()) })?;
    // Only this same runtime can consume the opaque IR; no disk cache exists.
    if unsafe { (backend.run)(ir.transfer()) } != 0 {
        return Err("execution IR interpreter process failed".into());
    }
    Ok(())
}
