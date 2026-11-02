import duplicate_prefix.S05ZeroCellActualCallInit
import duplicate_prefix.PositiveRootInstalledFrame
import duplicate_prefix.RootBlock0
import duplicate_prefix.SuccessfulTrace

/-! Exactly five actual statements after this closed call's proved
initialization. The Bool allocation is obtained from init's conclusion and is
otherwise abstract. No suffix safety or error-prefix theorem is asserted. -/
namespace DuplicatePrefix.S05ZeroCellActualCallFirstBlock
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext S05ZeroCellActualCallParameters S05ZeroCellJointPacket
open S05ZeroCellTypedGeneratedPrefix (tag)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

/-- Same Result configuration, empty-stack init and Unit/True choices. The
five successful transitions retain depth one and reach root block0/statement5. -/
theorem initializes_and_five (span : PreparedContracts.FixedSpanQuery)
    (cmp : ProjectionMetadataFacts.NullComparator) (source : PreparedContracts.SourceComparator) :
    let cfg := config options (remaining+1) span
    ∃ updated first second third fourth fifth,
      initializationResult span = .ok () (S05ZeroCellActualCallInit.installed span updated) ∧
      ExecutionMachine.step cfg limits () (S05ZeroCellActualCallInit.installed span updated) = (first,.ok true) ∧
      ExecutionMachine.step cfg limits () first = (second,.ok true) ∧
      ExecutionMachine.step cfg limits () second = (third,.ok true) ∧
      ExecutionMachine.step cfg limits () third = (fourth,.ok true) ∧
      ExecutionMachine.step cfg limits () fourth = (fifth,.ok true) ∧
      SuccessfulTrace.Trace cfg limits (S05ZeroCellActualCallInit.installed span updated) fifth ∧
      (S05ZeroCellActualCallInit.installed span updated).stack.frames.size = 1 ∧ fifth.stack.frames.size = 1 ∧
      fifth.stack.currentFrame?.map (·.location) = some (.mir ⟨0,5⟩) := by
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
  obtain ⟨first,second,third,fourth,fifth,h1,h2,h3,h4,h5,thirdEq,last,atLocation⟩ :=
    RootBlock0.actual_first_block_statements options limits remaining span source rfl #[] frame machine 1
      (body.trans raw.body) (identity.trans raw.identity) location (callee.trans raw.callee) size
      (congrArg LocalState.value s3) (congrArg LocalState.value s4) (congrArg LocalState.value s5)
      (congrArg LocalState.layout s4) (congrArg LocalState.layout s5) (by rw [size]; decide)
      (congrArg LocalState.value s2) (congrArg LocalState.layout s2) (noClocks.trans raw.noClocks)
      tracker tracked defaultMode ghost shallow remaining rfl
  refine ⟨updated,first,second,third,fourth,fifth,init,?_,h2,h3,h4,h5,?_,depth,?_,atLocation⟩
  · rw [state]; exact h1
  · rw [state]; exact .next h1 (.next h2 (.next h3 (.next h4 (.next h5 (.refl _)))))
  · rw [last]; rfl

end DuplicatePrefix.S05ZeroCellActualCallFirstBlock
