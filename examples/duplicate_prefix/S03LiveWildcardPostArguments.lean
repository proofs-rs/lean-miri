import duplicate_prefix.S03LiveWildcardInitTail
import duplicate_prefix.S03LiveWildcardPacket
import duplicate_prefix.S03ReturnWildcardMetadata
import duplicate_prefix.PositiveRootInstalledFrame
import duplicate_prefix.ConcreteEmptyRootArgumentProperties

namespace DuplicatePrefix.S03LiveWildcardPostArguments
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification RootFrameData
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Shared actual post-argument tail and current packet for both incoming live
argument provenances. The raw root and zero-tag data are outputs of the real
argument scope. Protection, uninit and pushDone derive all post-state fields;
no successful tail or future packet is supplied as a premise. -/
theorem run
    {options : EvalConfigurationCore.Options} {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
    (limits : ExecutionMachine.Limits) (before : Before)
    (model : DuplicatePrefixCallModel.Model options (remaining+1) span before)
    (place : MPlaceTy Provenance) (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global)
    (distinct : input.entry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder input.entry.allocation.extra)
    (nodeRoom : input.entry.allocation.extra.nodes.size+3 < 65536)
    (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (tagRoom : input.tracker.global.nextPointerTag.value.toNat+3 < 2^64)
    (wildcard : input.pointer.provenance = .wildcard)
    (zeroTag : BorTag) (zeroIndex : UniIndex)
    (zero : S03EmptyTagState.Data input.entry.allocation.extra zeroTag zeroIndex)
    (root : RootFrame)
    (raw : root.frame.locals = Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (rootReturn : root.frame.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩)
    (rootContinuation : root.frame.returnContinuation = .stop true) (rootVarargs : root.frame.vaList = #[])
    (address count : UInt64)
    (syncEmpty : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == input.id) =
      some (input.id,⟨none,#[]⟩))
    (notConstructed : before.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (thread : Miri.Concurrency.ThreadRecord) (active : before.threads.activeThread? = some thread)
    (topZero : thread.topUserRelevantFrame = some 0) :
    let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete input.id zeroTag) (Size.ofBytes address)) 0 ActualReferenceMetadata.reference).imm
    let args := RootArgumentsTwo.result (ConcreteEmptyRootArguments.firstDone root adjusted {} input.id zeroTag) count
    ∃ frame machine,
      RootEntryTail.tail (ExecutionMachine.callHooks (config options (remaining+1) span) limits) place
        (Storage.withCurrent #[] args.frame before) = .ok () (Storage.withCurrent #[] frame machine) ∧
      Nonempty (S03LiveWildcardPacket.Packet options remaining span frame machine place address count) := by
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete input.id zeroTag) (Size.ofBytes address)) 0 ActualReferenceMetadata.reference).imm
  let args := RootArgumentsTwo.result (ConcreteEmptyRootArguments.firstDone root adjusted {} input.id zeroTag) count
  let argumentFrame := ({} : FrameState).addProtector input.id zeroTag
  have frameBorrow : args.frame.extra.borrowTracker = some argumentFrame := rfl
  have slot (i : Fin 25) : root.frame.locals[i.val]'(root.valid i) = ⟨.dead,none⟩ := by
    have rows := congrArg (fun rows : Array (LocalState Provenance LocalLayout) => rows[i.val]?) raw
    have row : root.frame.locals[i.val]? = some (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
      simpa only [Array.getElem?_replicate,i.isLt,↓reduceIte] using rows
    exact Option.some.inj ((Array.getElem?_eq_getElem (root.valid i)).symm.trans row)
  have dead (i : Fin 25) (ne1 : i.val ≠ 1) (ne2 : i.val ≠ 2) :
      (args.frame.locals[i.val]'(args.valid i)).value = .dead := by
    rw [ConcreteEmptyRootArgumentProperties.untouched root adjusted {} input.id zeroTag count i ne1 ne2,slot i]
  obtain ⟨tree,updated,⟨tail,treeEq,byteSize,bytes,mutable,maskValid,maskLength,pointerBounds,capacity,growth,
      postRuntime,postShort,postDistinct,postOrder,postExposed,child,childTagged,roots,⟨childPositive⟩,activity,
      node,childPresent,returnSame,parentless,leaf,returnHidden⟩,⟨zeroAfter⟩,quiet,owned,hiddenFrame⟩ :=
    S03LiveWildcardInitTail.run limits before model place input runtime distinct order (by omega) fresh wildcard
      zeroTag zeroIndex zero #[] args.frame argumentFrame frameBorrow rfl #[] syncEmpty (by simp)
      args.body args.size (dead ⟨0,by decide⟩ (by decide) (by decide))
      (dead ⟨6,by decide⟩ (by decide) (by decide)) (dead ⟨13,by decide⟩ (by decide) (by decide))
      (dead ⟨14,by decide⟩ (by decide) (by decide)) args.noClocks args.identity args.callee
  let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker input.tracker fresh)
    input.tracker.global.nextPointerTag
  let written := (tree.performBorrowAccessRange (.concrete input.tracker.global.nextPointerTag)
    (Size.ofBytes input.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree
  let frame := PositiveRootInstalledFrame.installed root adjusted count {} input.id zeroTag input.id input.tracker.global.nextPointerTag
  let machine := (S04ProtectUninit.finished before place input #[] {args.frame with location := .unwinding ⟨601⟩}
    argumentFrame fresh tree updated).machine
  let tracker := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker input.tracker fresh) input.tracker.global.nextPointerTag
  let borrowFrame := argumentFrame.addProtector input.id input.tracker.global.nextPointerTag
  let destination := S03ReturnWildcardMetadata.of_protection input wildcard #[]
    {args.frame with location := .unwinding ⟨601⟩} argumentFrame fresh tree updated written
    treeEq byteSize bytes mutable maskValid maskLength pointerBounds capacity
  have differentTags : zeroTag ≠ input.tracker.global.nextPointerTag := Ne.symm
    (S03EmptyReturnConstructorFacts.fresh_ne input.entry.allocation.extra input.tracker.global.nextPointerTag zeroTag zeroIndex
      (GeneralBorrowParentTagInvariant.fresh _ _ runtime) zero.tagged)
  have originalPositive := input.borrow
  have binding := input.binding
  simp only [DuplicatePrefixReferenceInput.Binding,wildcard] at binding
  rw [binding.1] at originalPositive
  have oldNonempty := originalPositive.wildcardRoot rfl
  have notPrimary : ∀ valid : 0 < written.roots.size, written.roots[0] ≠ child := by
    intro valid same
    have rootsEq : written.roots = input.entry.allocation.extra.roots.push child := roots
    have rootAt : input.entry.allocation.extra.roots[0]'oldNonempty = child := by
      simpa only [rootsEq,Array.getElem_push_lt oldNonempty] using same
    have member : child ∈ input.entry.allocation.extra.roots.toList := by
      rw [←rootAt]
      exact Array.mem_toList_iff.mpr (Array.getElem_mem oldNonempty)
    have nodup : written.roots.toList.Nodup := postDistinct
    rw [rootsEq,Array.toList_push,List.nodup_append] at nodup
    exact nodup.2.2 child member child (by simp) rfl
  have bodyRoom : updated.extra.nodes.size+2 < 65536 := by rw [treeEq];omega
  have successor := GenericFunctionEntryNumerics.successor_value input.tracker.global.nextPointerTag fresh
  change global.nextPointerTag.value.toNat = input.tracker.global.nextPointerTag.value.toNat+1 at successor
  obtain ⟨oldTracker,oldEnabled,defaultMode⟩ := model.defaultTracker
  have sameTracker : oldTracker = input.tracker := Option.some.inj (oldEnabled.symm.trans input.enabled)
  subst oldTracker
  let currentModel := S03IntegerZeroState.retime model remaining
  have frameMeta := PositiveRootInstalledFrame.metadata root adjusted count {} input.id zeroTag input.id input.tracker.global.nextPointerTag
  have frameSize := PositiveRootInstalledFrame.size root adjusted count {} input.id zeroTag input.id input.tracker.global.nextPointerTag
  have slots := PositiveRootInstalledFrame.slot root raw adjusted count {} input.id zeroTag input.id input.tracker.global.nextPointerTag
  have immediate := PositiveRootInstalledFrame.immediate root raw adjusted count {} input.id zeroTag input.id input.tracker.global.nextPointerTag
  refine ⟨frame,machine,tail,⟨{
    tracker := tracker,borrowFrame := borrowFrame,destination := destination,
    zeroTag := zeroTag,zeroIndex := zeroIndex,
    zero := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact zeroAfter,
    quiet := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact quiet,
    returnTag := input.tracker.global.nextPointerTag,child := child,returnNode := node,differentTags := differentTags,
    defaultMode := defaultMode,enabled := rfl,frameTracked := frameMeta.2.2.2.2.2.2.2.1,owned := owned,
    returnTagged := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact childTagged,
    returnPresent := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact childPresent,
    returnSame := returnSame,parentless := parentless,leaf := leaf,returnHidden := returnHidden,
    hiddenFrame := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact hiddenFrame,
    runtime := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact postRuntime,
    positive := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact childPositive.base,
    distinct := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact postDistinct,
    order := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact postOrder,
    exposed := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact postExposed,
    notPrimary := by change ∀ valid : 0 < updated.extra.roots.size,updated.extra.roots[0] ≠ child;rw [treeEq];exact notPrimary,
    headroom := bodyRoom,fresh := UInt64.lt_iff_toNat_lt.mpr (by change global.nextPointerTag.value.toNat < 18446744073709551615;omega),
    tagRoomNext := by change global.nextPointerTag.value.toNat+1 < 18446744073709551615;omega,
    activity := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact activity,
    thread := thread,active := active,topZero := topZero,race := model.noDataRace,backend := model.noBackend,
    ghost := model.ghostOff,shallow := model.shallow,extras := syncEmpty,metadata := model.metadata,notConstructed := notConstructed,
    sourceBody := frameMeta.1.trans root.body,identity := frameMeta.2.1.trans root.identity,callee := frameMeta.2.2.1.trans root.callee,
    location := frameMeta.2.2.2.2.2.2.2.2,frameSize := frameSize,
    slots := by intro i;have point:=slots i;change frame.locals[i.val] = _ at point;rw [point];rfl,
    noLocalClocks := frameMeta.2.2.2.2.2.2.1.trans root.noClocks,
    returnPlace := by rw [frameMeta.2.2.2.2.1];exact rootReturn,
    continuation := frameMeta.2.2.2.1.trans rootContinuation,
    immediateLocals := immediate,varargs := frameMeta.2.2.2.2.2.1.trans rootVarargs,
    unchecked := currentModel.unchecked,noGc := currentModel.noGc,fixed := model.fixedScheduler }⟩⟩

end
end DuplicatePrefix.S03LiveWildcardPostArguments
