import Miri.Input.CompilerConstantMachine

/-! Negative regression for the cached compiler/runtime document binding.
The deliberately invalid site and absent frame ensure the mismatch guard
remains the first observable failure. -/

open Miri.Input Miri.Interpreter

private def document (raw : Lean.Json) : ImportDocument :=
  { producer := ⟨"miri", "rustc", "version", "target"⟩
    completenessStatus := .supported
    types := #[]
    allocations := #[]
    instances := #[]
    selectedScope := none
    functionAbis := #[]
    bodies := #[]
    typedTree := .scalar .null
    obligations := #[]
    raw := raw }

private def target : Miri.ABI.RuntimeTargetDataLayout := Id.run do
  let size : Miri.ABI.Size := ⟨8⟩
  let ptr : Miri.ABI.PointerSpec := ⟨size, .ONE, size, false⟩
  return ⟨⟨.little, .w64⟩, .ONE, .ONE, .ONE, .ONE, .ONE, .ONE,
    .ONE, .ONE, .ONE, .ONE, .ONE, #[], .ZERO, ptr, #[], .ZERO, .I32⟩

private def runtime : RuntimeMetadata :=
  { source := document (.str "runtime"), target, layouts := #[] }

private def prepared : CompilerConstantQueries.Prepared :=
  ⟨⟨⟨#[],#[],#[],#[]⟩, #[], #[], #[], document (.str "compiler")⟩, #[], #[]⟩

private def binding := CompilerConstantQueries.bind prepared runtime

#guard binding.compatible == false

private def functions : FunctionPointers.Hooks Unit Unit Unit :=
  { registry := fun _ => .empty
    putRegistry := fun _ _ => ()
    crossCrateInlineAlways := false
    inlineNever := fun _ => pure false
    chooseSalt := pure ⟨0, by decide⟩
    ptrGetAlloc := fun _ => pure none
    adjustRootPointer := fun alloc tag => pure ⟨⟨0⟩, .concrete alloc tag⟩
    importedFunction := fun _ => pure none }

private def initialState : MachineHooks.State Unit Unit :=
  ⟨.empty, ⟨Miri.Memory.MemoryState.empty, none, none, ⟨.MAIN_THREAD, [], [], false, false⟩, #[], #[], ()⟩⟩

private def boundMismatchResult :=
  (CompilerConstantMachine.evalAtBound binding ⟨0, ⟨0,0⟩, #[]⟩
    functions ⟨⟨8⟩⟩ (fun _ => pure ⟨⟨0⟩, .wildcard⟩)
    (fun _ => .unsupported "unused classifier")
    ⟨⟨0⟩, none, .Val .ZeroSized 0⟩).run initialState

private def legacyMismatchResult :=
  (CompilerConstantMachine.evalAt prepared runtime ⟨0, ⟨0,0⟩, #[]⟩
    functions ⟨⟨8⟩⟩ (fun _ => pure ⟨⟨0⟩, .wildcard⟩)
    (fun _ => .unsupported "unused classifier")
    ⟨⟨0⟩, none, .Val .ZeroSized 0⟩).run initialState

private def isMismatch (result : EStateM.Result StepError
    (MachineHooks.State Unit Unit) (OpTy Provenance)) : Bool :=
  match result with
  | .error (.invalidProgram message) _ =>
      message == "constant runtime/compiler evidence document mismatch"
  | _ => false

#guard isMismatch boundMismatchResult
#guard isMismatch legacyMismatchResult

#print axioms Miri.Input.RuntimeMetadata.Indexed.matchesSourceLeft_eq
