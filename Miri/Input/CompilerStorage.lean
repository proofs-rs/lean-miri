import Miri.Input.CompilerFrameContext
import Miri.Interpreter.DynamicLayout

/-! Source stack.rs storage_live_dyn's query-free type fast path and place.rs
allocate_dyn. This uses the original local type, not its normalized layout.
Compiler inference subtypes absent from the input remain explicit obligations. -/
namespace Miri.Input.CompilerStorage
open Lean Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

private def metadata (value : Except String A) : Except StepError A :=
  value.mapError (fun reason => .unsupported s!"storage type metadata: {reason}")

private def trivial (runtime : RuntimeMetadata) : Nat → TyId → Except StepError Bool
  | 0, _ => .error (.invalidProgram "cyclic compiler type in storage sizedness traversal")
  | fuel + 1, ty => do
    let node ← (runtime.node ty).mapError (fun e => StepError.unsupported (toString e))
    match node.shape with
    | .int _ | .uint _ | .bool | .float _ | .functionDefinition .. | .functionPointer ..
    | .rawPointer .. | .char | .reference .. | .coroutine .. | .array ..
    | .closure .. | .coroutineClosure .. | .never => pure true
    | .str | .slice _ | .dynamicTraitObject .. | .foreign _ | .adt _ | .alias .. => pure false
    | .tuple elements =>
      if elements.isEmpty then return true
      let some tail := elements[elements.size - 1]?
        | throw (.invalidProgram "nonempty compiler tuple has no tail")
      trivial runtime fuel tail
    | .patternType inner _ | .unsafeBinder inner _ => trivial runtime fuel inner

/-- Every recursive step follows a canonical type edge. The type-table length
bounds an acyclic path; exhaustion diagnoses malformed cyclic input, rather
than limiting MIR execution or returning an invented sizedness result. -/
def veryTriviallySized (runtime : RuntimeMetadata) (ty : TyId) : Except StepError Bool :=
  trivial runtime (runtime.source.types.size + 1) ty

/-- Actual source storage dictionary. The only allocation input is the real
stack allocator, and dynamic size/alignment queries execute before reserving
an allocation ID. Deallocation is the actual allocation-lifecycle operation. -/
def hooks [DecidableEq K] (p : CompilerProviders.Prepared)
    (allocation : PlaceMachine.AllocationConfig K U)
    (dynamic : DynamicLayoutHooks Provenance (MachineHooks.State K U) C)
    (dynamicBudget : Nat) (choice : C)
    (deallocateStack : Pointer (Option Provenance) → MachineHooks.M K U Unit) :
    MachineHooks.StorageHooks K U where
  veryTriviallySized := veryTriviallySized p.runtime
  layout := CompilerFrameContext.computeLocalLayout p
  allocateDyn := fun layout metadataValue => do
    let some (size,align) ← DynamicLayout.sizeAndAlignFromMeta dynamic choice dynamicBudget metadataValue layout
      | throw (.invalidProgram "cannot allocate space for extern type with unknown size")
    let pointer ← PlaceMachine.allocateStackRaw allocation size align
    pure ⟨pointer,metadataValue,none⟩
  deallocateStack := deallocateStack
end Miri.Input.CompilerStorage
