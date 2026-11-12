import Miri.Interpreter.FunctionPointers

/-! Pinned memory.rs::ptr_get_alloc_id carries the actual integer address, size
zero and Dereferenceable("pointer"). These equalities retain the entire machine
and frame state, including any state already produced by the resolution hook. -/
namespace MiriTests.FunctionPointerAllocationDiagnostics
open Miri.ABI Miri.Memory Miri.Interpreter
open Miri.Interpreter.FunctionPointers

variable {K U Other : Type}

private def dangling (address : UInt64) : StepError :=
  MemoryErrors.access (.danglingIntegerPointer address 0 (.dereferenceable "pointer"))

theorem noProvenance (h : Hooks K U Other) (address : UInt64)
    (state : MachineHooks.State K U) :
    allocation h (Pointer.withoutProvenance address) state =
      .error (dangling address) state := by
  rfl

theorem failedLookup (h : Hooks K U Other) (pointer : Pointer Provenance)
    (state after : MachineHooks.State K U)
    (lookup : h.ptrGetAlloc pointer state = .ok none after) :
    allocation h pointer.withOptionalProvenance state =
      .error (dangling pointer.offset.bytes) after := by
  simp [allocation, Pointer.intoPointerOrAddr, Pointer.withOptionalProvenance,
    Pointer.new, bind, pure, EStateM.bind, EStateM.pure, lookup, dangling] <;> rfl

theorem successfulLookup (h : Hooks K U Other) (pointer : Pointer Provenance)
    (state after : MachineHooks.State K U) (result : AllocId × Size)
    (lookup : h.ptrGetAlloc pointer state = .ok (some result) after) :
    allocation h pointer.withOptionalProvenance state = .ok result after := by
  simp [allocation, Pointer.intoPointerOrAddr, Pointer.withOptionalProvenance,
    Pointer.new, bind, pure, EStateM.bind, EStateM.pure, lookup, dangling] <;> rfl

theorem propagatedError (h : Hooks K U Other) (pointer : Pointer Provenance)
    (state after : MachineHooks.State K U) (error : StepError)
    (lookup : h.ptrGetAlloc pointer state = .error error after) :
    allocation h pointer.withOptionalProvenance state = .error error after := by
  simp [allocation, Pointer.intoPointerOrAddr, Pointer.withOptionalProvenance,
    Pointer.new, bind, pure, EStateM.bind, EStateM.pure, lookup, dangling] <;> rfl

theorem nonzeroFunctionOffset (h : Hooks K U Other)
    (pointer : Pointer (Option Provenance)) (state after : MachineHooks.State K U)
    (id : AllocId) (offset : Size)
    (lookup : allocation h pointer state = .ok (id, offset) after)
    (nonzero : (offset != .ZERO) = true) :
    getPtrFn h pointer state = .error (.undefinedBehavior "InvalidFunctionPointer") after := by
  simp [getPtrFn, bind, EStateM.bind, lookup, nonzero] <;> rfl

theorem nonfunctionAllocation (h : Hooks K U Other)
    (pointer : Pointer (Option Provenance)) (state after resolved : MachineHooks.State K U)
    (id : AllocId)
    (lookup : allocation h pointer state = .ok (id, .ZERO) after)
    (function : getFnAlloc h id after = .ok none resolved) :
    getPtrFn h pointer state = .error (.undefinedBehavior "InvalidFunctionPointer") resolved := by
  simp [getPtrFn, bind, EStateM.bind, lookup, function] <;> rfl

theorem functionSuccess (h : Hooks K U Other)
    (pointer : Pointer (Option Provenance)) (state after resolved : MachineHooks.State K U)
    (id : AllocId) (value : FnVal Other)
    (lookup : allocation h pointer state = .ok (id, .ZERO) after)
    (function : getFnAlloc h id after = .ok (some value) resolved) :
    getPtrFn h pointer state = .ok value resolved := by
  simp [getPtrFn, bind, pure, EStateM.bind, EStateM.pure, lookup, function] <;> rfl


end MiriTests.FunctionPointerAllocationDiagnostics
