import duplicate_prefix.PhysicalValidityMemory
import duplicate_prefix.ScalarCopyStage
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace DuplicatePrefix.PhysicalPrimitiveValidity
open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open Miri.Memory.Validity
open Lean Elab
elab "range_set_mk" : term => do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith ".DataRangeSet.mk" then some name else none
  match names with
  | [name] => return mkConst name
  | _ => throwError "missing unique source range-set constructor"

elab "physical_reset_padding" : term => do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith ".ValidityVisitor.resetPadding" then some name else none
  match names with
  | [name] => return mkConst name
  | _ => throwError "missing unique source padding helper"

theorem add_empty_full (offset size : Size)
    (positive : size ≠ Size.ZERO)
    (finish : Size) (endpoint : (allocRange offset size).endExclusive = .ok finish) :
    DataRangeSet.empty.addRange offset size = .ok (range_set_mk #[allocRange offset size]) := by
  unfold DataRangeSet.addRange
  have nonzero : (size == Size.ZERO) = false := by simp [positive]
  rw [nonzero]
  simp only [Bool.false_eq_true, ↓reduceIte, endpoint, Except.mapError,
    bind, Except.bind, pure, Except.pure, DataRangeSet.empty]
  unfold_internal ".DataRangeSet.splitBefore"
  rfl

theorem visit_boolean_memory
    (hooks : ValidityVisitor.Hooks Provenance S C E F A Pad) (choice : C) (fuel : Nat)
    (session : ValidityVisitor.Session Provenance) (mplace : MemPlace Provenance) (layout : LocalLayout)
    (state : S) (value : Bool)
    (classification : hooks.classify choice layout.ty state = .ok .boolean state)
    (read : hooks.readImmediate choice ⟨.memory mplace,layout⟩ .boolean state = .ok ⟨.scalar (Scalar.fromBool value),layout⟩ state)
    (clear : hooks.clearProvenance choice ⟨.memory mplace,layout⟩ state = .ok () state)
    (operand : hooks.toOp choice ⟨.memory mplace,layout⟩ state = .ok ⟨.indirect mplace,layout⟩ state)
    (reset : session.flags.resetProvenanceAndPadding = true)
    (ranges : session.dataBytes = some .empty)
    (sized : layout.layout.isSized = true)
    (positive : layout.layout.size ≠ Size.ZERO)
    (finish : Size) (endpoint : (allocRange mplace.ptr.offset layout.layout.size).endExclusive = .ok finish) :
    ValidityVisitor.visit hooks choice (fuel + 1) session ⟨.memory mplace,layout⟩ state =
      .ok {session with dataBytes := some (range_set_mk #[allocRange mplace.ptr.offset layout.layout.size])} state := by
  have added := add_empty_full mplace.ptr.offset layout.layout.size positive finish endpoint
  unfold ValidityVisitor.visit
  unfold_internal ".ValidityVisitor.primitive"
  unfold_internal ".ValidityVisitor.scalarOf"
  unfold_internal ".ValidityVisitor.liftResult"
  unfold_internal ".ValidityVisitor.markPlace"
  unfold_internal ".ValidityVisitor.dataOffset"
  unfold_internal ".ValidityVisitor.markRange"
  unfold_internal ".ValidityVisitor.rangeResult"
  simp only [classification, read, clear, operand, reset, ranges, sized, added,
    Immediate.toScalar, Except.mapError, ScalarOperations.bool_scalar_roundtrip,
    bind, EStateM.bind, pure, EStateM.pure]
  unfold_internal ".ValidityVisitor.liftResult"
  simp [clear, operand, added, Except.mapError, bind, EStateM.bind, pure, EStateM.pure]

theorem padding_memory_complete
    (hooks : ValidityVisitor.Hooks Provenance S C E F A Pad) (choice : C)
    (session : ValidityVisitor.Session Provenance) (mplace : MemPlace Provenance) (layout : LocalLayout)
    (state : S)
    (ranges : session.dataBytes = some (range_set_mk #[allocRange mplace.ptr.offset layout.layout.size]))
    (size : hooks.sizeAndAlign choice ⟨mplace,layout⟩ state =
      .ok (some (layout.layout.size,layout.layout.align.abi)) state) :
    physical_reset_padding hooks choice session ⟨.memory mplace,layout⟩ state = .ok () state := by
  unfold_internal ".ValidityVisitor.resetPadding"
  simp [ranges, forceAllocation, size, DataRangeSet.toArray, bind, EStateM.bind, pure, EStateM.pure]

theorem validate_boolean_memory {K U C F A Pad : Type}
    (hooks : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A Pad)
    (choice : C) (fuel : Nat) (state : ValidityMachine.State K U)
    (mplace : MemPlace Provenance) (layout : LocalLayout) (value : Bool) (name : String)
    (ghost : state.machine.user.payload.ghost = false)
    (named : hooks.typeName choice layout.ty = pure name)
    (withGhost : hooks.withGhostValidation (A := ValidityVisitor.Session Provenance) =
      @ValidityMachine.withGhostValidation K U (ValidityVisitor.Session Provenance))
    (active : ValidityMachine.State K U)
    (activeEq : active = {state with machine := {state.machine with user := {state.machine.user with
      payload := {state.machine.user.payload with ghost := true}}}})
    (classification : hooks.classify choice layout.ty active = .ok .boolean active)
    (read : hooks.readImmediate choice ⟨.memory mplace,layout⟩ .boolean active = .ok ⟨.scalar (Scalar.fromBool value),layout⟩ active)
    (clear : hooks.clearProvenance choice ⟨.memory mplace,layout⟩ active = .ok () active)
    (operand : hooks.toOp choice ⟨.memory mplace,layout⟩ active = .ok ⟨.indirect mplace,layout⟩ active)
    (size : hooks.sizeAndAlign choice ⟨mplace,layout⟩ active =
      .ok (some (layout.layout.size,layout.layout.align.abi)) active)
    (sized : layout.layout.isSized = true) (positive : layout.layout.size ≠ Size.ZERO)
    (finish : Size) (endpoint : (allocRange mplace.ptr.offset layout.layout.size).endExclusive = .ok finish) :
    ValidityVisitor.validatePlace hooks choice (fuel + 1) ⟨.memory mplace,layout⟩ false true state = .ok () state := by
  let initial : ValidityVisitor.Session Provenance := {
    path := ⟨name,#[]⟩, flags := ⟨true,false⟩, ctfeMode := none, refTracking := none, dataBytes := some .empty }
  let visited := {initial with dataBytes := some (range_set_mk #[allocRange mplace.ptr.offset layout.layout.size])}
  have visit := visit_boolean_memory hooks choice fuel initial mplace layout active value classification read clear operand
    rfl rfl sized positive finish endpoint
  have padding := padding_memory_complete hooks choice visited mplace layout active rfl size
  unfold ValidityVisitor.validatePlace
  rw [named]
  simp only [bind, EStateM.bind, pure, EStateM.pure, Bool.false_eq_true, ↓reduceIte]
  rw [withGhost]
  unfold ValidityMachine.withGhostValidation
  simp only [ghost, Bool.false_eq_true, ↓reduceIte]
  simp only [bind, EStateM.bind]
  rw [← activeEq]
  erw [operand]
  simp only [bind, EStateM.bind]
  erw [visit]
  simp only [bind, EStateM.bind]
  erw [padding]
  simp only [pure, EStateM.pure]
  subst active
  have restored : {state.machine.user.payload with ghost := false} = state.machine.user.payload := by rw [← ghost]
  simp only [restored, ↓reduceIte]

#print axioms validate_boolean_memory

#print axioms padding_memory_complete

#print axioms visit_boolean_memory
end DuplicatePrefix.PhysicalPrimitiveValidity

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.PhysicalPrimitiveValidity.validate_boolean_memory,
      ``DuplicatePrefix.PhysicalPrimitiveValidity.add_empty_full,
      ``DuplicatePrefix.PhysicalPrimitiveValidity.visit_boolean_memory,
      ``DuplicatePrefix.PhysicalPrimitiveValidity.padding_memory_complete] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved physical primitive validity dependency {dependency}"
