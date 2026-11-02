import duplicate_prefix.S05ZeroCellActualCallInit
import duplicate_prefix.PositiveRootInstalledFrame
import duplicate_prefix.GenericFunctionEntryPrefix
import duplicate_prefix.SuccessfulTrace

/-! The existing structural nonzero-count prefix, stopping before the shared
reference expression that prepares the len helper call. This is an actual
source Trace, with no new borrowing case. -/
namespace DuplicatePrefix.S05ZeroCellActualCallToLen
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext S05ZeroCellActualCallParameters S05ZeroCellJointPacket
open S05ZeroCellTypedGeneratedPrefix (tag)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

/-- Same closed init and Result configuration; stop before the shared
expression, retaining the existing structural Shape for source analysis. -/
theorem initializes_to_len (span : PreparedContracts.FixedSpanQuery)
    (cmp : ProjectionMetadataFacts.NullComparator) (source : PreparedContracts.SourceComparator) :
    let cfg := config options (remaining+1) span
    ∃ updated result,
      let after := Storage.withCurrent #[] result (RootZeroCompleteState.tick options remaining span
        (S05ZeroCellActualCallInit.installed span updated).machine)
      initializationResult span = .ok () (S05ZeroCellActualCallInit.installed span updated) ∧
      SuccessfulTrace.Trace cfg limits (S05ZeroCellActualCallInit.installed span updated) after ∧
      GenericFunctionEntryPrefix.Shape ((S05ZeroCellActualCallInit.installed span updated).stack.frames[0]'(by change 0 < 1; decide)) result 1 ∧
      (S05ZeroCellActualCallInit.installed span updated).stack.frames.size = 1 ∧ after.stack.frames.size = 1 ∧
      after.stack.currentFrame?.map (·.location) = some (.mir ⟨2,11⟩) := by
  obtain ⟨updated,init,depth⟩ := S05ZeroCellActualCallInit.init_ok span cmp
  let raw := RawRootInvocation.root before place profile.2.2.2.1
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete sourceId (tag 8)) (Size.ofBytes 4096)) 2 ActualReferenceMetadata.reference).imm
  let frame := PositiveRootInstalledFrame.installed raw adjusted 1 {} sourceId (tag 8) destinationId (tag 9)
  let machine := (S05ZeroCellActualCallInit.installed span updated).machine
  have state : S05ZeroCellActualCallInit.installed span updated = Storage.withCurrent #[] frame machine := rfl
  obtain ⟨body,identity,callee,continuation,returnPlace,vaList,noClocks,borrow,location⟩ :=
    PositiveRootInstalledFrame.metadata raw adjusted 1 {} sourceId (tag 8) destinationId (tag 9)
  have size : frame.locals.size = 25 := PositiveRootInstalledFrame.size raw adjusted 1 {} sourceId (tag 8) destinationId (tag 9)
  have slot (i : Fin 25) := PositiveRootInstalledFrame.slot_option raw
    (RawRootInvocation.locals before place profile.2.2.2.1) adjusted 1 {} sourceId (tag 8) destinationId (tag 9) i
  have getSlot (i : Fin 25) (value : LocalState Provenance LocalLayout)
      (row : frame.locals[i.val]? = some value) :
      (frame.locals[i.val]'(by rw [size]; exact i.isLt)) = value :=
    Option.some.inj ((Array.getElem?_eq_getElem (by rw [size]; exact i.isLt)).symm.trans row)
  have s3 := getSlot ⟨3,by decide⟩ ⟨.dead,none⟩ (by simpa [frame] using slot ⟨3,by decide⟩)
  have s4 := getSlot ⟨4,by decide⟩ ⟨.dead,none⟩ (by simpa [frame] using slot ⟨4,by decide⟩)
  have s5 := getSlot ⟨5,by decide⟩ ⟨.dead,none⟩ (by simpa [frame] using slot ⟨5,by decide⟩)
  have s2 := getSlot ⟨2,by decide⟩
    ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 1)))),some RootCompilerFacts.usizeLayout⟩
    (by simpa [frame] using slot ⟨2,by decide⟩)
  let tracker := machine.borrowTracker.get (by rfl)
  have tracked : machine.borrowTracker = some tracker := rfl
  have defaultMode : tracker.retagMode = .Default := rfl
  have ghost : machine.user.payload.ghost = false := rfl
  have shallow : machine.user.payload.validation = .Shallow := rfl
  have unused (id : Nat) (valid : id < frame.locals.size) (lo : 7 ≤ id) (hi : id ≤ 12) :
      frame.locals[id] = ⟨.dead,none⟩ := by
    have bounded : id < 25 := by omega
    have known := slot ⟨id,bounded⟩
    apply getSlot ⟨id,bounded⟩ ⟨.dead,none⟩
    simpa only [Fin.val_mk,
      show 14 ≠ id by omega, show 13 ≠ id by omega, show 6 ≠ id by omega,
      show 0 ≠ id by omega, show 2 ≠ id by omega, show 1 ≠ id by omega,
      false_or,ite_false] using known
  have immediate := PositiveRootInstalledFrame.immediate raw
    (RawRootInvocation.locals before place profile.2.2.2.1) adjusted 1 {} sourceId (tag 8) destinationId (tag 9)
  have flags : ((config options (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false ∧
      ((config options (remaining+1) span).terminators.getControl machine.user).gcInterval = 0 := by
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact ⟨rfl,rfl⟩
  obtain ⟨result,trace,shape⟩ := GenericFunctionEntryPrefix.executes_preserving options limits remaining span source rfl
    remaining rfl frame machine 1 (by decide) size (congrArg LocalState.value s2) (congrArg LocalState.layout s2)
    (congrArg LocalState.value s3) (congrArg LocalState.layout s3)
    (congrArg LocalState.value s4) (congrArg LocalState.value s5)
    (congrArg LocalState.layout s4) (congrArg LocalState.layout s5) unused
    (body.trans raw.body) (identity.trans raw.identity) (callee.trans raw.callee) location
    (noClocks.trans raw.noClocks) immediate tracker tracked defaultMode ghost shallow flags.1 flags.2 (by rfl)
  refine ⟨updated,result,init,?_,shape,depth,rfl,?_⟩
  · rw [state]; exact trace
  · simp only [Storage.withCurrent,Stack.currentFrame?,Array.back?_push,Option.map_some,shape.location]

end DuplicatePrefix.S05ZeroCellActualCallToLen
