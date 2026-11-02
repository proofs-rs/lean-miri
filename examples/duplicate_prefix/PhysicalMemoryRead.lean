import duplicate_prefix.PhysicalMemoryWrite
import duplicate_prefix.PhysicalBoolRead
import duplicate_prefix.RootCompilerFacts
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.PhysicalMemoryRead
open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open Lean Elab
private def sourceName (suffix : String) : CoreM Name := do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix then some name else none
  match names with
  | [name] => pure name
  | _ => throwError "expected unique physical read helper {suffix}"
elab "operand_read_plan" : term => return mkConst (← sourceName ".Miri.Interpreter.readPlan")
elab "scalar_read_plan" : term => return mkConst (← sourceName ".Miri.Interpreter.ImmediateReadPlan.scalar")

theorem bool_read_plan (runtime : RuntimeTargetDataLayout) :
    operand_read_plan (localMemoryLayout RootCompilerFacts.boolLayout) runtime =
      .ok (some (scalar_read_plan (Size.ofBytes 1) false)) := by
  with_unfolding_all rfl

theorem bool_raw_of_allocation {Extra K S PX : Type} [DecidableEq K]
    (memory : MemoryState Provenance Extra K) (hooks : S)
    (place : MemoryOperandPlace Provenance) (runtime : RuntimeTargetDataLayout)
    (globalKind : Option K) (globals : GlobalAllocationHooks Provenance Extra K S)
    (accessHooks : AllocationAccessHooks Provenance Extra K S PX)
    (dynamic : DynamicLayoutResolver Provenance Extra K S)
    (id : AllocId) (allocation : Allocation Provenance Extra) (value : Bool)
    (layout : place.layout = localMemoryLayout RootCompilerFacts.boolLayout)
    (access : getPlaceAlloc memory hooks place runtime true globalKind globals accessHooks dynamic =
      ⟨memory,hooks,some ⟨id,allocRange Size.ZERO (Size.ofBytes 1),allocation⟩,
        .ok (some ⟨id,allocRange Size.ZERO (Size.ofBytes 1),allocation⟩)⟩)
    (read : Allocation.readScalar allocation runtime.base (allocRange Size.ZERO (Size.ofBytes 1)) false =
      .ok (Scalar.fromBool value)) :
    readImmediateFromMplaceRaw memory hooks place runtime true globalKind globals accessHooks dynamic =
      ⟨memory,hooks,some ⟨id,allocRange Size.ZERO (Size.ofBytes 1),allocation⟩,
        .ok (some ⟨.scalar (Scalar.fromBool value),place.layout⟩)⟩ := by
  have sized : place.layout.backendRepr.isUnsized = false := by rw [layout]; decide +kernel
  unfold readImmediateFromMplaceRaw
  simp only [sized, Bool.false_eq_true, ↓reduceIte, Bind.bind, Pure.pure, Id.instMonad]
  rw [access]
  simp only [Bind.bind, Pure.pure, Id.instMonad]
  have plan : operand_read_plan place.layout runtime = .ok (some (scalar_read_plan (Size.ofBytes 1) false)) := by
    rw [layout]
    exact bool_read_plan runtime
  erw [plan]
  simp only [Bind.bind, Pure.pure, Id.instMonad]
  unfold_internal ".Miri.Interpreter.readScalarAt"
  unfold_internal ".Miri.Interpreter.componentRange"
  simp only [PhysicalMemoryWrite.subrange_full, Except.mapError, Bind.bind, Pure.pure, Except.bind, Except.pure]
  erw [read]
  rfl

elab "primitive_readable" : term => return mkConst (← sourceName ".Miri.Interpreter.isPrimitiveReadable")

theorem bool_immediate_of_raw {Extra K S PX : Type} [DecidableEq K]
    (memory : MemoryState Provenance Extra K) (hooks : S) (mplace : MemPlace Provenance)
    (runtime : RuntimeTargetDataLayout) (globalKind : Option K)
    (globals : GlobalAllocationHooks Provenance Extra K S)
    (accessHooks : AllocationAccessHooks Provenance Extra K S PX)
    (dynamic : DynamicLayoutResolver Provenance Extra K S)
    (id : AllocId) (allocation : Allocation Provenance Extra) (value : Bool)
    (raw : readImmediateFromMplaceRaw memory hooks ⟨mplace,localMemoryLayout RootCompilerFacts.boolLayout⟩
      runtime true globalKind globals accessHooks dynamic =
      ⟨memory,hooks,some ⟨id,allocRange Size.ZERO (Size.ofBytes 1),allocation⟩,
        .ok (some ⟨.scalar (Scalar.fromBool value),localMemoryLayout RootCompilerFacts.boolLayout⟩)⟩) :
    Miri.Interpreter.readImmediate memory hooks (.indirect mplace) (localMemoryLayout RootCompilerFacts.boolLayout)
      runtime true globalKind globals accessHooks dynamic =
      ⟨memory,hooks,some ⟨id,allocRange Size.ZERO (Size.ofBytes 1),allocation⟩,
        .ok ⟨.scalar (Scalar.fromBool value),localMemoryLayout RootCompilerFacts.boolLayout⟩⟩ := by
  have readable : primitive_readable (localMemoryLayout RootCompilerFacts.boolLayout).backendRepr = true := by
    with_unfolding_all rfl
  unfold Miri.Interpreter.readImmediate Miri.Interpreter.readImmediateRaw
  simp only [readable, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bind.bind, Pure.pure, Id.instMonad]
  rw [raw]
  simp only [Bind.bind, Pure.pure, Id.instMonad]
  rfl

#print axioms bool_immediate_of_raw

#print axioms bool_raw_of_allocation
end DuplicatePrefix.PhysicalMemoryRead
open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.PhysicalMemoryRead.bool_read_plan,
      ``DuplicatePrefix.PhysicalMemoryRead.bool_raw_of_allocation,
      ``DuplicatePrefix.PhysicalMemoryRead.bool_immediate_of_raw] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved physical memory read dependency {dependency}"
