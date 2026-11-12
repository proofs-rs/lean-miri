import Miri.ABI.ExternAbi

/-! Pinned rustc_abi/src/extern_abi.rs150–164 and ordered ALL_VARIANTS179–222.
These are enum encoding/source spelling operations, not ABI classification. -/
namespace Miri.ABI.ExternAbi
private def variants : Array ExternAbi := #[
  .C false,.C true,.Rust,.Swift,.Aapcs false,.Aapcs true,
  .AvrInterrupt,.AvrNonBlockingInterrupt,.Cdecl false,.Cdecl true,
  .CmseNonSecureCall,.CmseNonSecureEntry,.Custom,.EfiApi,
  .Fastcall false,.Fastcall true,.GpuKernel,.LlvmIntrinsic,.Msp430Interrupt,
  .PtxKernel,.RiscvInterruptM,.RiscvInterruptS,.RustCall,.RustCold,
  .RustInvalid,.RustPreserveNone,.Stdcall false,.Stdcall true,
  .System false,.System true,.SysV64 false,.SysV64 true,.RustTail,
  .Thiscall false,.Thiscall true,.Vectorcall false,.Vectorcall true,
  .Win64 false,.Win64 true,.X86Interrupt]

def ofPacked (value : Nat) : Except String ExternAbi :=
  match variants[value]? with
  | some abi => pure abi
  | none => .error "packed ExternAbi is outside the pinned enum"

def asPacked (abi : ExternAbi) : Nat :=
  variants.toList.idxOf abi

private def withUnwind (name : String) (unwind : Bool) : String :=
  if unwind then name ++ "-unwind" else name

def asStr : ExternAbi → String
  | .C unwind => withUnwind "C" unwind
  | .System unwind => withUnwind "system" unwind
  | .Rust => "Rust" | .RustCall => "rust-call" | .RustCold => "rust-cold"
  | .RustInvalid => "rust-invalid" | .RustPreserveNone => "rust-preserve-none"
  | .RustTail => "tail" | .LlvmIntrinsic => "llvm-intrinsic" | .Custom => "custom"
  | .EfiApi => "efiapi" | .Swift => "Swift"
  | .Aapcs unwind => withUnwind "aapcs" unwind
  | .CmseNonSecureCall => "cmse-nonsecure-call" | .CmseNonSecureEntry => "cmse-nonsecure-entry"
  | .GpuKernel => "gpu-kernel" | .PtxKernel => "ptx-kernel"
  | .AvrInterrupt => "avr-interrupt" | .AvrNonBlockingInterrupt => "avr-non-blocking-interrupt"
  | .Msp430Interrupt => "msp430-interrupt" | .RiscvInterruptM => "riscv-interrupt-m"
  | .RiscvInterruptS => "riscv-interrupt-s" | .X86Interrupt => "x86-interrupt"
  | .Cdecl unwind => withUnwind "cdecl" unwind
  | .Stdcall unwind => withUnwind "stdcall" unwind
  | .Fastcall unwind => withUnwind "fastcall" unwind
  | .Thiscall unwind => withUnwind "thiscall" unwind
  | .Vectorcall unwind => withUnwind "vectorcall" unwind
  | .SysV64 unwind => withUnwind "sysv64" unwind
  | .Win64 unwind => withUnwind "win64" unwind
end Miri.ABI.ExternAbi
