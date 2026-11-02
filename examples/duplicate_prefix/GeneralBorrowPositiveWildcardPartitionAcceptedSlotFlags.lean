import duplicate_prefix.GeneralBorrowPositiveWildcardPartitionAcceptedUnheld
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardPartitionAcceptedSlotFlags
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open GeneralBorrowPositiveWildcardPartitionAcceptedInput GeneralBorrowPositiveWildcardPartitionNonzeroInput GeneralBorrowPositiveWildcardPartitionAcceptedUnheld
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

theorem registered_ended_absent (tracker : MachineHooks.BorrowState) (id : AllocId) (key query : BorTag)
    (absent : tracker.global.protectedTags.contains query=false) :
    ((TypedBorrowSteps.registeredGlobal tracker key).endCall (({} : FrameState).addProtector id key)).protectedTags.contains query=false := by
  by_cases same : query=key
  · subst query
    exact GeneralBorrowRelease.end_call_owned_absent _ _ id key (by simp [FrameState.addProtector])
  · apply end_absent
    exact insert_absent _ key query _ same absent

theorem registered_ended_held (tracker : MachineHooks.BorrowState) (id : AllocId) (key query : BorTag)
    (different : query≠key) (held : tracker.global.protectedTags.contains query=true) :
    ((TypedBorrowSteps.registeredGlobal tracker key).endCall (({} : FrameState).addProtector id key)).protectedTags.contains query=true := by
  change ((tracker.global.protectedTags.insert key .StrongProtector).remove key).contains query=true
  unfold ProtectedTags.contains at held ⊢
  rw [GeneralBorrowProtectorCacheMap.remove_other _ key query different,ProtectorInsertion.get_other _ key query _ different]
  exact held

theorem inserted_held (tags : ProtectedTags) (key : BorTag) (kind : ProtectorKind) :
    (tags.insert key kind).contains key=true := by
  apply (GeneralBorrowRelease.contains_iff_entry (tags.insert key kind) key).mpr
  exact ⟨(key,kind),by simp [ProtectedTags.insert],rfl⟩

variable [area : GeneralBorrowExposedKnownRootState.Scope]

/-- Actual helper insertions may temporarily protect the bool-slot root if it
aliases a future helper tag; that helper's real endCall removes it again. The
bool-slot child is distinct from both helper tags and remains held throughout.
No freshness condition on the slot root versus future helper tags is assumed. -/
theorem after_mutable (s : GeneralBorrowPositiveWildcardPartitionAcceptedInput.Initial) :
    (mutableEnded s).protectedTags.contains s.slotRoot=false ∧
    (mutableEnded s).protectedTags.contains (GeneralBorrowPositiveWildcardPartitionFunctionState.next s.tracker s.fresh).global.nextPointerTag=true := by
  let first:=s.tracker.global.nextPointerTag
  let slot:=(GeneralBorrowPositiveWildcardPartitionFunctionState.next s.tracker s.fresh).global.nextPointerTag
  let lenTag:=helperTag s.toBase
  let mutTag:=(mutableTracker s).global.nextPointerTag
  have heldFree : (held s.toBase).global.protectedTags.contains s.slotRoot=false := by
    change ((s.tracker.global.protectedTags.insert first .StrongProtector).insert slot .StrongProtector).contains s.slotRoot=false
    exact insert_absent _ slot s.slotRoot _ s.slotDistinct (insert_absent _ first s.slotRoot _ s.slotParentDistinct s.slotFree)
  have slotHeld : (held s.toBase).global.protectedTags.contains slot=true := by
    change ((s.tracker.global.protectedTags.insert first .StrongProtector).insert slot .StrongProtector).contains slot=true
    exact inserted_held _ slot .StrongProtector
  have numbers:=GeneralBorrowPositiveWildcardPartitionAcceptedNumerics.values s
  have slotNat:=GenericFunctionEntryNumerics.successor_value s.tracker.global.nextPointerTag s.fresh
  change slot.value.toNat=first.value.toNat+1 at slotNat
  have lenNat : lenTag.value.toNat=first.value.toNat+3:=numbers.2.1
  have mutNat : mutTag.value.toNat=first.value.toNat+5:=numbers.2.2.2
  have slotLen : slot≠lenTag := by intro equal;have same:=congrArg (fun tag : BorTag=>tag.value.toNat) equal;omega
  have slotMut : slot≠mutTag := by intro equal;have same:=congrArg (fun tag : BorTag=>tag.value.toNat) equal;omega
  have lenFree : (lenEnded s.toInitial).global.protectedTags.contains s.slotRoot=false :=
    registered_ended_absent (ReferenceBorrowDriver.allocatedTracker (expressionTracker s.toBase) s.helperFresh) s.id lenTag s.slotRoot heldFree
  have lenSlot : (lenEnded s.toInitial).global.protectedTags.contains slot=true :=
    registered_ended_held (ReferenceBorrowDriver.allocatedTracker (expressionTracker s.toBase) s.helperFresh) s.id lenTag slot slotLen slotHeld
  exact ⟨registered_ended_absent (ReferenceBorrowDriver.allocatedTracker (mutableTracker s) s.mutableHelperFresh) s.id mutTag s.slotRoot lenFree,
    registered_ended_held (ReferenceBorrowDriver.allocatedTracker (mutableTracker s) s.mutableHelperFresh) s.id mutTag slot slotMut lenSlot⟩
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardPartitionAcceptedSlotFlags
