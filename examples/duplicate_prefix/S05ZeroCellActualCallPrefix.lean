import duplicate_prefix.S05ZeroCellActualCallInit
import duplicate_prefix.PositiveRootInstalledFrame
import duplicate_prefix.RootPrefix
import duplicate_prefix.SuccessfulTrace

/-! Exactly three actual StorageLive steps after this closed call's proved
initialization. The Bool allocation is obtained from init's conclusion and is
otherwise abstract. No suffix safety or error-prefix theorem is asserted. -/
namespace DuplicatePrefix.S05ZeroCellActualCallPrefix
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext S05ZeroCellActualCallParameters S05ZeroCellJointPacket
open S05ZeroCellTypedGeneratedPrefix (tag)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

/-- Same Result configuration, empty-stack init and Unit/True choices. The
three successful transitions retain depth one and reach root block0/statement3. -/
theorem initializes_and_three (span : PreparedContracts.FixedSpanQuery)
    (cmp : ProjectionMetadataFacts.NullComparator) :
    let cfg := config options (remaining+1) span
    ∃ updated first second third,
      initializationResult span = .ok () (S05ZeroCellActualCallInit.installed span updated) ∧
      ExecutionMachine.step cfg limits () (S05ZeroCellActualCallInit.installed span updated) = (first,.ok true) ∧
      ExecutionMachine.step cfg limits () first = (second,.ok true) ∧
      ExecutionMachine.step cfg limits () second = (third,.ok true) ∧
      SuccessfulTrace.Trace cfg limits (S05ZeroCellActualCallInit.installed span updated) third ∧
      (S05ZeroCellActualCallInit.installed span updated).stack.frames.size = 1 ∧ third.stack.frames.size = 1 ∧
      third.stack.currentFrame?.map (·.location) = some (.mir ⟨0,3⟩) := by
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
  have dead (i : Fin 25) (row : frame.locals[i.val]? = some (⟨.dead,none⟩ : LocalState Provenance LocalLayout)) :
      (frame.locals[i.val]'(by rw [size]; exact i.isLt)).value = .dead :=
    congrArg LocalState.value (Option.some.inj ((Array.getElem?_eq_getElem (by rw [size]; exact i.isLt)).symm.trans row))
  obtain ⟨first,second,third,h1,h2,h3,last,sameMachine,atLocation⟩ := RootPrefix.actual_initial_storage
    options (remaining+1) span limits #[] frame machine (body.trans raw.body) location size
    (dead ⟨3,by decide⟩ (by simpa [frame] using slot ⟨3,by decide⟩))
    (dead ⟨4,by decide⟩ (by simpa [frame] using slot ⟨4,by decide⟩))
    (dead ⟨5,by decide⟩ (by simpa [frame] using slot ⟨5,by decide⟩)) (noClocks.trans raw.noClocks)
  refine ⟨updated,first,second,third,init,?_,h2,h3,?_,depth,?_,atLocation⟩
  · rw [state]; exact h1
  · rw [state]; exact .next h1 (.next h2 (.next h3 (.refl _)))
  · rw [last]; rfl

end DuplicatePrefix.S05ZeroCellActualCallPrefix
