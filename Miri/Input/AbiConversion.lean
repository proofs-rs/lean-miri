import Miri.Input.CallCompatibility
import Miri.ABI.FnAbi
import Miri.Interpreter.Call

/-! Checked conversion of canonical physical ABI records. This layer has no
instance/body preparation or compiler query catalogs. -/
namespace Miri.Input.AbiConversion
open Lean Miri.ABI Miri.Interpreter
abbrev Result := Except String
private def require (value : Option A) (message : String) : Result A :=
  match value with | some value => pure value | none => throw message

def convention (source : CanonicalAbi) : Result CanonAbi := do
  match source.kind with
  | .c => pure .C | .rust => pure .Rust | .rustCold => pure .RustCold
  | .rustPreserveNone => pure .RustPreserveNone | .rustTail => pure .RustTail
  | .custom => pure .Custom | .swift => pure .Swift | .gpuKernel => pure .GpuKernel
  | .arm =>
    let call ← require source.armCall "missing Arm calling convention"
    return .Arm (← match call with
      | .aapcs => pure ArmCall.Aapcs | .cmseNonSecureCall => pure .CCmseNonSecureCall
      | .cmseNonSecureEntry => pure .CCmseNonSecureEntry)
  | .interrupt =>
    let kind ← require source.interruptKind "missing interrupt calling convention"
    return .Interrupt (← match kind with
      | .avr => pure InterruptKind.Avr | .avrNonBlocking => pure .AvrNonBlocking
      | .msp430 => pure .Msp430 | .riscvMachine => pure .RiscvMachine
      | .riscvSupervisor => pure .RiscvSupervisor | .x86 => pure .X86)
  | .x86 =>
    let call ← require source.x86Call "missing x86 calling convention"
    return .X86 (← match call with
      | .fastcall => pure X86Call.Fastcall | .stdcall => pure .Stdcall | .sysv64 => pure .SysV64
      | .thiscall => pure .Thiscall | .vectorcall => pure .Vectorcall | .win64 => pure .Win64)

def functionAbi (runtime : RuntimeMetadata) (source : FunctionAbi) : Result (FnAbi TypeId) := do
  let args ← source.arguments.mapM fun argument => (CallCompatibility.argument runtime argument).mapError toString
  let ret ← (CallCompatibility.argument runtime source.returnValue).mapError toString
  if source.fixedCount >= 2^32 then throw "FnAbi.fixed_count exceeds u32"
  if source.fixedCount > args.size then throw "FnAbi.fixed_count exceeds actual arguments"
  -- rustc's physical `FnAbi.args` can include the compiler-injected caller
  -- location while `fixed_count` counts only explicit source arguments.
  -- Preserve both exact facts here; demanded call initialization validates
  -- their relationship against the exact `requires_caller_location` query.
  return ⟨args,ret,source.cVariadic,UInt32.ofNat source.fixedCount,← convention source.callingConvention,source.canUnwind⟩

/-- The input carries only an ABI table reference. Conversion to the semantic
ABI happens when an operation requests it; input graphs are never expanded. -/
def functionAbiId (runtime : RuntimeMetadata) (id : Nat) : Result (FnAbi TypeId) := do
  let source ← require runtime.source.functionAbis[id]? s!"compiler FnAbi ID {id} out of bounds"
  functionAbi runtime source

end Miri.Input.AbiConversion
