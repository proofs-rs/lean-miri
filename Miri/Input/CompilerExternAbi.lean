import Miri.Input.JsonReader
import Miri.ABI.ExternAbi

namespace Miri.Input.CompilerExternAbi
open JsonReader

private structure decodeFields where
  «kind» : Option (String) := none
  «unwind» : Option (Option Bool) := none

def decode  : Parser (ABI.ExternAbi) := do
  let s ← object (decodeFields.mk none none) fun s key => do
    match key with
    | "kind" => return { s with «kind» := some (← string) }
    | "unwind" => return { s with «unwind» := some (← nullable boolean) }
    | _ => skipValue; pure s
  let kind := (← required s.«kind» "kind")
  let unwind := (← required s.«unwind» "unwind")
  match kind with
  | "c" => return .C (← required unwind "unwind boolean")
  | "system" => return .System (← required unwind "unwind boolean")
  | "rust" => do
    unless unwind.isNone do fail "non-unwind ExternAbi variant contains an unwind field"
    pure .Rust
  | "rust_call" => do
    unless unwind.isNone do fail "non-unwind ExternAbi variant contains an unwind field"
    pure .RustCall
  | "rust_cold" => do
    unless unwind.isNone do fail "non-unwind ExternAbi variant contains an unwind field"
    pure .RustCold
  | "rust_invalid" => do
    unless unwind.isNone do fail "non-unwind ExternAbi variant contains an unwind field"
    pure .RustInvalid
  | "rust_preserve_none" => do
    unless unwind.isNone do fail "non-unwind ExternAbi variant contains an unwind field"
    pure .RustPreserveNone
  | "rust_tail" => do
    unless unwind.isNone do fail "non-unwind ExternAbi variant contains an unwind field"
    pure .RustTail
  | "llvm_intrinsic" => do
    unless unwind.isNone do fail "non-unwind ExternAbi variant contains an unwind field"
    pure .LlvmIntrinsic
  | "custom" => do
    unless unwind.isNone do fail "non-unwind ExternAbi variant contains an unwind field"
    pure .Custom
  | "efi_api" => do
    unless unwind.isNone do fail "non-unwind ExternAbi variant contains an unwind field"
    pure .EfiApi
  | "swift" => do
    unless unwind.isNone do fail "non-unwind ExternAbi variant contains an unwind field"
    pure .Swift
  | "aapcs" => return .Aapcs (← required unwind "unwind boolean")
  | "cmse_nonsecure_call" => do
    unless unwind.isNone do fail "non-unwind ExternAbi variant contains an unwind field"
    pure .CmseNonSecureCall
  | "cmse_nonsecure_entry" => do
    unless unwind.isNone do fail "non-unwind ExternAbi variant contains an unwind field"
    pure .CmseNonSecureEntry
  | "gpu_kernel" => do
    unless unwind.isNone do fail "non-unwind ExternAbi variant contains an unwind field"
    pure .GpuKernel
  | "ptx_kernel" => do
    unless unwind.isNone do fail "non-unwind ExternAbi variant contains an unwind field"
    pure .PtxKernel
  | "avr_interrupt" => do
    unless unwind.isNone do fail "non-unwind ExternAbi variant contains an unwind field"
    pure .AvrInterrupt
  | "avr_non_blocking_interrupt" => do
    unless unwind.isNone do fail "non-unwind ExternAbi variant contains an unwind field"
    pure .AvrNonBlockingInterrupt
  | "msp430_interrupt" => do
    unless unwind.isNone do fail "non-unwind ExternAbi variant contains an unwind field"
    pure .Msp430Interrupt
  | "riscv_interrupt_machine" => do
    unless unwind.isNone do fail "non-unwind ExternAbi variant contains an unwind field"
    pure .RiscvInterruptM
  | "riscv_interrupt_supervisor" => do
    unless unwind.isNone do fail "non-unwind ExternAbi variant contains an unwind field"
    pure .RiscvInterruptS
  | "x86_interrupt" => do
    unless unwind.isNone do fail "non-unwind ExternAbi variant contains an unwind field"
    pure .X86Interrupt
  | "cdecl" => return .Cdecl (← required unwind "unwind boolean")
  | "stdcall" => return .Stdcall (← required unwind "unwind boolean")
  | "fastcall" => return .Fastcall (← required unwind "unwind boolean")
  | "thiscall" => return .Thiscall (← required unwind "unwind boolean")
  | "vectorcall" => return .Vectorcall (← required unwind "unwind boolean")
  | "sysv64" => return .SysV64 (← required unwind "unwind boolean")
  | "win64" => return .Win64 (← required unwind "unwind boolean")
  | _ => fail "unknown compiler ExternAbi variant"

end Miri.Input.CompilerExternAbi
