import duplicate_prefix.S03NonliveInstalledPacket
import duplicate_prefix.S03NonliveMetadataTag
import duplicate_prefix.S03NonliveReturnBounds
import duplicate_prefix.S03NonliveCallResources
import duplicate_prefix.SuccessfulTraceTerminal

namespace DuplicatePrefix.S03NonlivePositiveContract
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification S05ConsistentCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Initial-data result for the nonzero-count nonlive concrete empty-input branch.
The actual initialization produces the packet consumed by the body and original
Return. The initial sixteen-tag margin supplies both remaining body retags. -/
theorem complete {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before} {pointer : Pointer Provenance}
    {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (tag : BorTag) (concrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id tag)
    (argumentId : AllocId) (parentTag : BorTag) (argumentConcrete : pointer.provenance = .concrete argumentId parentTag)
    (argumentMetadata : DuplicatePrefixEmptyReferenceInput.Metadata before.memory argumentId (some parentTag))
    (argumentAbsent : before.memory.live.find? (fun row => row.1 == argumentId) = none)
    (count : UInt64) (nonzero : count ≠ 0) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer pointer) 0 count place := by
  let facts := S03NonliveCallResources.of_contract input argumentId parentTag argumentConcrete
  let model := input.contract.model
  let destination := input.contract.destination
  have metadataNone := S03NonliveMetadataTag.changeTag before.memory argumentId (some parentTag) none argumentMetadata argumentAbsent
  obtain ⟨updated,entry,treeEq,byteSize,bytes,mutable,maskValid,maskLength,pointerBounds,
    postRuntime,postOrder,child,childTagged,⟨childPositive⟩,activity⟩ := S03NonliveZeroInit.enters limits before model
      place destination facts.runtime facts.distinct facts.order facts.headroom facts.first facts.second tag concrete
      argumentId parentTag facts.base facts.offset count facts.nonzero facts.cached argumentMetadata argumentAbsent facts.dynamicFuel facts.validityFuel facts.dynamicEq facts.validityEq
      input.slice_not_constructed input.return_extras input.contract.thread input.contract.active input.contract.emptyHarnessCache
  let start := S03NonliveZeroInit.installed destination facts.runtime model.noDataRace argumentId facts.base facts.offset count facts.first facts.second tag updated
  let adjusted := (RetagReferencePlace.sliceValue PreparedReflection.actual.runtime.target.base
    (Pointer.new (.concrete argumentId destination.tracker.global.nextPointerTag) (Size.ofBytes (facts.base+facts.offset)))
      0 ActualReferenceMetadata.reference).imm
  let frame := PositiveRootInstalledFrame.installed (RawRootInvocation.root before place model.noDataRace)
    adjusted count {} argumentId destination.tracker.global.nextPointerTag destination.id
      (TypedRetagGeneric.protectedGlobal destination.tracker.global facts.first).nextPointerTag
  obtain ⟨packet⟩ := S03NonliveInstalledPacket.of_result before model place destination facts.runtime facts.distinct facts.order
    facts.headroom facts.first facts.second tag concrete argumentId facts.base facts.offset count metadataNone argumentAbsent input.slice_not_constructed input.return_extras
    input.contract.thread input.contract.active updated treeEq byteSize bytes mutable maskValid maskLength pointerBounds
    postRuntime postOrder child childTagged childPositive activity
  have actualTracked : start.machine.borrowTracker = some (S03NonliveCallResources.held destination.tracker facts.first facts.second) := rfl
  have trackerEq : packet.tracker = S03NonliveCallResources.held destination.tracker facts.first facts.second :=
    Option.some.inj (packet.enabled.symm.trans actualTracked)
  have bodyFresh : packet.tracker.global.nextPointerTag.value < 18446744073709551615 := by
    rw [trackerEq];exact facts.bodyFresh
  have bodyRoom : packet.tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615 := by
    rw [trackerEq];exact facts.bodyRoom
  have nextTag : packet.tracker.global.nextPointerTag = facts.tags 2 := by rw [trackerEq];exact facts.bodyTag
  have lenTag : (ReferenceBorrowDriver.allocatedTracker packet.tracker bodyFresh).global.nextPointerTag = facts.tags 3 := by
    simpa only [ReferenceBorrowDriver.allocatedTracker,TypedRetagEmpty.successorTag,trackerEq] using facts.lenTag
  have unused : ∀ id (valid : id < frame.locals.size), 7 ≤ id → id ≤ 12 → frame.locals[id] = ⟨.dead,none⟩ := by
    intro id valid lower upper
    have bounded : id < 25 := by rw [←packet.frameSize];exact valid
    have slot := packet.slots ⟨id,bounded⟩
    simpa only [Fin.val_mk,show ¬(14=id ∨ 13=id ∨ 6=id ∨ 0=id) by omega,
      show ¬2=id by omega,show ¬1=id by omega,↓reduceIte] using slot
  obtain ⟨done,trace,terminal,empty,noErrors,noUb⟩ := S03NonliveReturnBounds.complete options limits remaining span frame start.machine
    packet.tracker packet.borrowFrame packet.defaultMode packet.enabled packet.frameTracked place packet.destination
    packet.returnTag packet.child packet.selected packet.maximum packet.returnNode packet.argument
    packet.returnTagged packet.returnPresent packet.returnSame packet.returnEdge packet.returnHidden packet.hiddenFrame
    packet.runtime packet.positive packet.distinct (fun _ _ => packet.order) packet.short packet.activity
    packet.thread packet.active packet.topZero packet.race packet.backend packet.ghost packet.shallow
    #[] packet.extras (by simp) facts.validityFuel facts.dynamicFuel facts.budget facts.dynamicEq facts.dispatchEq
    model.preciseOff model.implicitOff model.nullComparator bodyFresh bodyRoom packet.metadata packet.notConstructed
    model.debugOff facts.validityEq (DuplicatePrefixCallModel.sourceComparator _ _ _ _ model)
    packet.sourceBody packet.identity packet.callee packet.location packet.frameSize
    (by simpa using congrArg (fun row => row.value) (packet.slots ⟨0,by decide⟩))
    (by simpa using congrArg (fun row => row.layout) (packet.slots ⟨0,by decide⟩))
    (by simpa using congrArg (fun row => row.value) (packet.slots ⟨3,by decide⟩))
    (by simpa using congrArg (fun row => row.value) (packet.slots ⟨4,by decide⟩))
    (by simpa using congrArg (fun row => row.value) (packet.slots ⟨5,by decide⟩))
    (by simpa using congrArg (fun row => row.layout) (packet.slots ⟨4,by decide⟩))
    (by simpa using congrArg (fun row => row.layout) (packet.slots ⟨5,by decide⟩))
    (by simpa using congrArg (fun row => row.layout) (packet.slots ⟨3,by decide⟩))
    facts.tags facts.tagsDistinct argumentId none facts.base facts.offset count facts.nonzero nonzero
    packet.argumentMetadata packet.argumentAbsent facts.cached nextTag lenTag
    (by simpa only [CanonicalConfigFacts.actual_access_runtime,facts.firstTag,Fin.val_mk,Nat.reduceEqDiff,or_false,↓reduceIte] using
      congrArg (fun row => row.value) (packet.slots ⟨1,by decide⟩))
    (by simpa using congrArg (fun row => row.layout) (packet.slots ⟨1,by decide⟩)) unused
    (by simpa using congrArg (fun row => row.value) (packet.slots ⟨13,by decide⟩))
    (by simpa using congrArg (fun row => row.layout) (packet.slots ⟨13,by decide⟩))
    (by simpa using congrArg (fun row => row.value) (packet.slots ⟨2,by decide⟩))
    (by simpa using congrArg (fun row => row.layout) (packet.slots ⟨2,by decide⟩))
    packet.noLocalClocks packet.returnPlace packet.continuation packet.immediateLocals packet.varargs
    packet.unchecked packet.noGc packet.fixed
  have incoming : Pointer.new (.concrete argumentId parentTag) (Size.ofBytes (facts.base+facts.offset)) = pointer := by
    have address := facts.address
    cases pointer with
    | mk off provenance =>
      change provenance = .concrete argumentId parentTag at argumentConcrete
      subst provenance
      cases off with
      | mk bytes => simp only [Pointer.new,Size.ofBytes] at address ⊢;rw [address]
  refine ⟨start,done,?_,trace,terminal,empty,noErrors,noUb,SuccessfulTraceTerminal.prefix_step_success trace terminal⟩
  simpa only [DuplicatePrefixSliceArgument.first,DuplicatePrefixSliceArgument.rawValue,incoming] using entry

end
end DuplicatePrefix.S03NonlivePositiveContract
