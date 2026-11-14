import Miri.ABI.CallConv
import Miri.ABI.ExternAbi

/-! Complete canonical calling-convention and FnAbi records from pinned
rustc_abi/canon_abi.rs and rustc_target/callconv/mod.rs:660–679. Target ABI
classification is supplied by the compiler, not recomputed by this module. -/
namespace Miri.ABI
inductive ArmCall where
  | Aapcs | CCmseNonSecureCall | CCmseNonSecureEntry
  deriving DecidableEq, Repr
inductive InterruptKind where
  | Avr | AvrNonBlocking | Msp430 | RiscvMachine | RiscvSupervisor | X86
  deriving DecidableEq, Repr
inductive X86Call where
  | Fastcall | Stdcall | SysV64 | Thiscall | Vectorcall | Win64
  deriving DecidableEq, Repr
inductive CanonAbi where
  | C | Rust | RustCold | RustPreserveNone | RustTail | Custom | Swift
  | Arm (call : ArmCall)
  | GpuKernel
  | Interrupt (kind : InterruptKind)
  | X86 (call : X86Call)
  deriving DecidableEq, Repr
namespace CanonAbi

def isRusticAbi : CanonAbi → Bool
  | .Rust | .RustCold | .RustPreserveNone | .RustTail => true
  | .C | .Custom | .Swift | .Arm _ | .GpuKernel | .Interrupt _ | .X86 _ => false
end CanonAbi
structure FnAbi (Ty : Type) where
  args : Array (ArgAbi Ty)
  ret : ArgAbi Ty
  cVariadic : Bool
  fixedCount : UInt32
  conv : CanonAbi
  canUnwind : Bool
  deriving DecidableEq, Repr
end Miri.ABI

namespace Miri.ABI

structure UnwindDefinition where
  neverUnwind : Bool
  foreignItem : Bool
  dropGlue : Bool
  deriving BEq, Repr, DecidableEq

/-- Raw dependencies of pinned rustc_middle::ty::layout::fn_can_unwind
(layout.rs:1310–1374), independent of the canonical calling convention. -/
structure UnwindSeed where
  abi : ExternAbi
  definition : Option UnwindDefinition
  panicUnwinds : Bool
  panicInDropUnwinds : Bool
  deriving BEq, Repr, DecidableEq

namespace UnwindSeed

def canUnwind (seed : UnwindSeed) : Bool :=
  if seed.definition.any (fun d => d.neverUnwind ||
      (!seed.panicUnwinds && !d.foreignItem) ||
      (!seed.panicInDropUnwinds && d.dropGlue)) then false
  else match seed.abi with
  | .C unwind | .System unwind | .Cdecl unwind | .Stdcall unwind
  | .Fastcall unwind | .Vectorcall unwind | .Thiscall unwind | .Aapcs unwind
  | .Win64 unwind | .SysV64 unwind => unwind
  | .Rust | .RustCall | .RustCold | .RustPreserveNone | .RustTail => seed.panicUnwinds
  | _ => false

end UnwindSeed
end Miri.ABI
