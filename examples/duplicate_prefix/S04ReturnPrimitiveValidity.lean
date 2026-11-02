import duplicate_prefix.PhysicalPrimitiveValidity
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace DuplicatePrefix.S04ReturnPrimitiveValidity
open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open Miri.Memory.Validity
theorem visit_boolean_memory
    (hooks : ValidityVisitor.Hooks Provenance S C E F A Pad) (choice : C) (fuel : Nat)
    (session : ValidityVisitor.Session Provenance) (mplace : MemPlace Provenance) (layout : LocalLayout)
    (state after : S) (value : Bool)
    (classification : hooks.classify choice layout.ty state = .ok .boolean state)
    (read : hooks.readImmediate choice ⟨.memory mplace,layout⟩ .boolean state = .ok ⟨.scalar (Scalar.fromBool value),layout⟩ state)
    (clear : hooks.clearProvenance choice ⟨.memory mplace,layout⟩ state = .ok () after)
    (operand : hooks.toOp choice ⟨.memory mplace,layout⟩ after = .ok ⟨.indirect mplace,layout⟩ after)
    (reset : session.flags.resetProvenanceAndPadding = true)
    (ranges : session.dataBytes = some .empty)
    (sized : layout.layout.isSized = true)
    (positive : layout.layout.size ≠ Size.ZERO)
    (finish : Size) (endpoint : (allocRange mplace.ptr.offset layout.layout.size).endExclusive = .ok finish) :
    ValidityVisitor.visit hooks choice (fuel + 1) session ⟨.memory mplace,layout⟩ state =
      .ok {session with dataBytes := some (range_set_mk #[allocRange mplace.ptr.offset layout.layout.size])} after := by
  have added := PhysicalPrimitiveValidity.add_empty_full mplace.ptr.offset layout.layout.size positive finish endpoint
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

theorem validate_boolean_memory {K U C F A Pad : Type}
    (hooks : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A Pad)
    (choice : C) (fuel : Nat) (state : ValidityMachine.State K U)
    (after : ValidityMachine.State K U)
    (afterGhost : after.machine.user.payload.ghost = false)
    (mplace : MemPlace Provenance) (layout : LocalLayout) (value : Bool) (name : String)
    (ghost : state.machine.user.payload.ghost = false)
    (named : hooks.typeName choice layout.ty = pure name)
    (withGhost : hooks.withGhostValidation (A := ValidityVisitor.Session Provenance) =
      @ValidityMachine.withGhostValidation K U (ValidityVisitor.Session Provenance))
    (active : ValidityMachine.State K U)
    (activeEq : active = {state with machine := {state.machine with user := {state.machine.user with
      payload := {state.machine.user.payload with ghost := true}}}})
    (activeAfter : ValidityMachine.State K U)
    (activeAfterEq : activeAfter = {after with machine := {after.machine with user := {after.machine.user with
      payload := {after.machine.user.payload with ghost := true}}}})
    (operandAfter : hooks.toOp choice ⟨.memory mplace,layout⟩ activeAfter =
      .ok ⟨.indirect mplace,layout⟩ activeAfter)
    (classification : hooks.classify choice layout.ty active = .ok .boolean active)
    (read : hooks.readImmediate choice ⟨.memory mplace,layout⟩ .boolean active = .ok ⟨.scalar (Scalar.fromBool value),layout⟩ active)
    (clear : hooks.clearProvenance choice ⟨.memory mplace,layout⟩ active = .ok () activeAfter)
    (operand : hooks.toOp choice ⟨.memory mplace,layout⟩ active = .ok ⟨.indirect mplace,layout⟩ active)
    (size : hooks.sizeAndAlign choice ⟨mplace,layout⟩ activeAfter =
      .ok (some (layout.layout.size,layout.layout.align.abi)) activeAfter)
    (sized : layout.layout.isSized = true) (positive : layout.layout.size ≠ Size.ZERO)
    (finish : Size) (endpoint : (allocRange mplace.ptr.offset layout.layout.size).endExclusive = .ok finish) :
    ValidityVisitor.validatePlace hooks choice (fuel + 1) ⟨.memory mplace,layout⟩ false true state = .ok () after := by
  let initial : ValidityVisitor.Session Provenance := {
    path := ⟨name,#[]⟩, flags := ⟨true,false⟩, ctfeMode := none, refTracking := none, dataBytes := some .empty }
  let visited := {initial with dataBytes := some (range_set_mk #[allocRange mplace.ptr.offset layout.layout.size])}
  have visit := visit_boolean_memory hooks choice fuel initial mplace layout active activeAfter value classification read clear operandAfter
    rfl rfl sized positive finish endpoint
  have padding := PhysicalPrimitiveValidity.padding_memory_complete hooks choice visited mplace layout activeAfter rfl size
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
  subst activeAfter
  have restored : {after.machine.user.payload with ghost := false} = after.machine.user.payload := by rw [← afterGhost]
  simp only [restored, ↓reduceIte]

end DuplicatePrefix.S04ReturnPrimitiveValidity
