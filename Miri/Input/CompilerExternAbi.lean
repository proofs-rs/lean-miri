import Lean
import Miri.ABI.ExternAbi

/-! Validates the exact structured compiler ExternAbi variant fields. Diagnostic
spelling and target canonical convention do not participate in source identity. -/
namespace Miri.Input.CompilerExternAbi
open Lean

private def requiredUnwind : Option Bool → Except String Bool
  | some value => pure value
  | none => throw "compiler ExternAbi requires an unwind flag"

def ofFields (kind : String) (unwind : Option Bool) : Except String ABI.ExternAbi := do
  match kind with
  | "c" => return .C (← requiredUnwind unwind)
  | "system" => return .System (← requiredUnwind unwind)
  | "rust" => do
    unless unwind.isNone do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .Rust
  | "rust_call" => do
    unless unwind.isNone do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .RustCall
  | "rust_cold" => do
    unless unwind.isNone do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .RustCold
  | "rust_invalid" => do
    unless unwind.isNone do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .RustInvalid
  | "rust_preserve_none" => do
    unless unwind.isNone do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .RustPreserveNone
  | "rust_tail" => do
    unless unwind.isNone do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .RustTail
  | "llvm_intrinsic" => do
    unless unwind.isNone do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .LlvmIntrinsic
  | "custom" => do
    unless unwind.isNone do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .Custom
  | "efi_api" => do
    unless unwind.isNone do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .EfiApi
  | "swift" => do
    unless unwind.isNone do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .Swift
  | "aapcs" => return .Aapcs (← requiredUnwind unwind)
  | "cmse_nonsecure_call" => do
    unless unwind.isNone do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .CmseNonSecureCall
  | "cmse_nonsecure_entry" => do
    unless unwind.isNone do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .CmseNonSecureEntry
  | "gpu_kernel" => do
    unless unwind.isNone do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .GpuKernel
  | "ptx_kernel" => do
    unless unwind.isNone do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .PtxKernel
  | "avr_interrupt" => do
    unless unwind.isNone do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .AvrInterrupt
  | "avr_non_blocking_interrupt" => do
    unless unwind.isNone do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .AvrNonBlockingInterrupt
  | "msp430_interrupt" => do
    unless unwind.isNone do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .Msp430Interrupt
  | "riscv_interrupt_machine" => do
    unless unwind.isNone do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .RiscvInterruptM
  | "riscv_interrupt_supervisor" => do
    unless unwind.isNone do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .RiscvInterruptS
  | "x86_interrupt" => do
    unless unwind.isNone do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .X86Interrupt
  | "cdecl" => return .Cdecl (← requiredUnwind unwind)
  | "stdcall" => return .Stdcall (← requiredUnwind unwind)
  | "fastcall" => return .Fastcall (← requiredUnwind unwind)
  | "thiscall" => return .Thiscall (← requiredUnwind unwind)
  | "vectorcall" => return .Vectorcall (← requiredUnwind unwind)
  | "sysv64" => return .SysV64 (← requiredUnwind unwind)
  | "win64" => return .Win64 (← requiredUnwind unwind)
  | _ => throw "unknown compiler ExternAbi variant"

def decode (source : Json) : Except String ABI.ExternAbi := do
  unless (← (← source.getObjVal? "status").getStr?) == "supported" do
    throw "compiler ExternAbi is unsupported"
  let input ← source.getObjVal? "unwind"
  let unwind ← if input == .null then pure none else some <$> input.getBool?
  ofFields (← (← source.getObjVal? "kind").getStr?) unwind

end Miri.Input.CompilerExternAbi
