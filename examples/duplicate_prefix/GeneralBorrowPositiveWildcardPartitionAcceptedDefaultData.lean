import duplicate_prefix.GeneralBorrowPositiveWildcardPartitionAcceptedNumerics
import duplicate_prefix.GeneralBorrowExposedScopedPostLenDefaultResources
import duplicate_prefix.GeneralBorrowExposedScopedSharedSourceSize
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardPartitionAcceptedDefaultData
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open GeneralBorrowPositiveWildcardPartitionAcceptedInput GeneralBorrowPositiveWildcardPartitionNonzeroInput
open GeneralBorrowFreshMetadataChildShared
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
abbrev held (i : GeneralBorrowExposedScopedLenCallInput.Input) :=
  TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker i.tracker i.fresh) i.tracker.global.nextPointerTag
abbrev ended (i : GeneralBorrowExposedScopedLenCallInput.Input) :=
  (held i).global.endCall (({} : FrameState).addProtector i.id i.input.newTag)
abbrev tracker (i : GeneralBorrowExposedScopedLenCallInput.Input) : MachineHooks.BorrowState :=
  {held i with global:=ended i}
abbrev released (i : GeneralBorrowExposedScopedLenCallInput.Input) :=
  ((GeneralBorrowExposedScopedSharedPathMetadata.child i.input (held i).global.protectedTags .VisitChildrenOfAccessed).releaseProtector i.input.newTag (held i).global.protectedTags).tree

theorem tracker_eq (s : GeneralBorrowPositiveWildcardPartitionAcceptedInput.Initial) (updated : Allocation Provenance BorrowTree)
    (i : GeneralBorrowExposedScopedLenCallInput.Input)
    (origin : GeneralBorrowPositiveWildcardPartitionNonzeroMachinePrefixMetadata.Origin s.toInitial updated i) :
    tracker i=lenEnded s.toInitial := by
  unfold tracker ended held
  simp only [i.tagEq,origin.tracker,origin.id,lenEnded,lenHeld]

theorem fresh (s : GeneralBorrowPositiveWildcardPartitionAcceptedInput.Initial) (updated : Allocation Provenance BorrowTree)
    (i : GeneralBorrowExposedScopedLenCallInput.Input)
    (origin : GeneralBorrowPositiveWildcardPartitionNonzeroMachinePrefixMetadata.Origin s.toInitial updated i) :
    (tracker i).global.nextPointerTag.value<18446744073709551615 := by
  rw [tracker_eq s updated i origin]
  exact s.mutableFresh

theorem next_fresh (s : GeneralBorrowPositiveWildcardPartitionAcceptedInput.Initial) (updated : Allocation Provenance BorrowTree)
    (i : GeneralBorrowExposedScopedLenCallInput.Input)
    (origin : GeneralBorrowPositiveWildcardPartitionNonzeroMachinePrefixMetadata.Origin s.toInitial updated i) :
    (ReferenceBorrowDriver.allocatedTracker (tracker i) (fresh s updated i origin)).global.nextPointerTag.value<18446744073709551615 := by
  have step:=GenericFunctionEntryNumerics.successor_value (tracker i).global.nextPointerTag (fresh s updated i origin)
  change (ReferenceBorrowDriver.allocatedTracker (tracker i) (fresh s updated i origin)).global.nextPointerTag.value.toNat=(tracker i).global.nextPointerTag.value.toNat+1 at step
  have same:=congrArg (fun t : MachineHooks.BorrowState=>t.global.nextPointerTag.value.toNat) (tracker_eq s updated i origin)
  change (tracker i).global.nextPointerTag.value.toNat=(mutableTag s.toInitial).value.toNat at same
  have expected:=GenericFunctionEntryNumerics.successor_value (mutableTag s.toInitial) s.mutableFresh
  change (ReferenceBorrowDriver.allocatedTracker (lenEnded s.toInitial) s.mutableFresh).global.nextPointerTag.value.toNat=(mutableTag s.toInitial).value.toNat+1 at expected
  have bound:=UInt64.lt_iff_toNat_lt.mp s.mutableHelperFresh
  rw [UInt64.lt_iff_toNat_lt]
  omega

/-- Original future reserves and source helper metadata form the actual
post-len Default mutable resources, including clean next slot and future helper
freshness. No post-len ownership, allocator or operation outcome is an input. -/
theorem prepare (s : GeneralBorrowPositiveWildcardPartitionAcceptedInput.Initial) (updated : Allocation Provenance BorrowTree)
    (i : GeneralBorrowExposedScopedLenCallInput.Input)
    (origin : GeneralBorrowPositiveWildcardPartitionNonzeroMachinePrefixMetadata.Origin s.toInitial updated i) :
    ∃ data : GeneralBorrowExposedScopedMutableEntryRaw.Data (released i) (tracker i).global.protectedTags
        i.first.parentNode.tag (tracker i).global.nextPointerTag i.input.offset i.input.len i.selected i.head i.tail,
      data.input.parent=i.first.parent ∧ data.input.offset=0 ∧ data.input.len=data.input.tree.locations.size.bytes ∧
      GeneralRangeMapState.Every (fun location : LocationTree=>location.perms.get (GeneralBorrowFreshMetadataChildDefault.index data.input)=none) data.input.tree.locations ∧
      GeneralBorrowGcVacantClean.VacantClean (released i) ∧ GeneralBorrowGcAllocator.NodeTags (released i) ∧
      (released i).nodes.size+2<65536 ∧ GeneralBorrowTagMap.Fresh (released i).tagMapping
        (ReferenceBorrowDriver.allocatedTracker (tracker i) (fresh s updated i origin)).global.nextPointerTag := by
  let future := (tracker i).global.nextPointerTag
  let reserve := (ReferenceBorrowDriver.allocatedTracker (tracker i) (fresh s updated i origin)).global.nextPointerTag
  have numerical := GeneralBorrowPositiveWildcardPartitionAcceptedNumerics.values s
  have futureEq : future=mutableTag s.toInitial :=
    congrArg (fun t : MachineHooks.BorrowState=>t.global.nextPointerTag) (tracker_eq s updated i origin)
  have futureValue : future.value.toNat=s.tracker.global.nextPointerTag.value.toNat+4 :=
    (congrArg (fun tag : BorTag=>tag.value.toNat) futureEq).trans numerical.2.2.1
  have reserveValue : reserve.value.toNat=s.tracker.global.nextPointerTag.value.toNat+5 := by
    have step:=GenericFunctionEntryNumerics.successor_value future (fresh s updated i origin)
    change reserve.value.toNat=future.value.toNat+1 at step
    omega
  have reserveEq : reserve=(ReferenceBorrowDriver.allocatedTracker (lenEnded s.toInitial) s.mutableFresh).global.nextPointerTag := by
    have valueEq : reserve.value=(ReferenceBorrowDriver.allocatedTracker (lenEnded s.toInitial) s.mutableFresh).global.nextPointerTag.value :=
      UInt64.toNat_inj.mp (reserveValue.trans numerical.2.2.2.symm)
    cases a : reserve with
    | mk value nonzero =>
      cases b : (ReferenceBorrowDriver.allocatedTracker (lenEnded s.toInitial) s.mutableFresh).global.nextPointerTag with
      | mk nextValue nextNonzero =>
        simp only [a,b] at valueEq
        cases valueEq
        rfl
  have rootFuture : s.tracker.global.nextPointerTag≠future := by
    intro same;have equal:=congrArg (fun tag : BorTag=>tag.value.toNat) same;omega
  have rootReserve : s.tracker.global.nextPointerTag≠reserve := by
    intro same;have equal:=congrArg (fun tag : BorTag=>tag.value.toNat) same;omega
  have futureInitial : GeneralBorrowTagMap.Fresh s.entry.allocation.extra.tagMapping future := by
    rw [futureEq]
    exact s.mutableMapFresh
  have reserveInitial : GeneralBorrowTagMap.Fresh s.entry.allocation.extra.tagMapping reserve := by
    rw [reserveEq]
    exact s.mutableHelperMapFresh
  have futureFresh : GeneralBorrowTagMap.Fresh i.first.tree.tagMapping future := by
    rw [origin.firstTree]
    exact GeneralBorrowFreshMetadataChildAllocator.fresh_push s.entry.allocation.extra.tagMapping s.tracker.global.nextPointerTag future
      ⟨UInt32.ofNat s.entry.allocation.extra.tagMapping.mapping.size⟩ s.entry.allocation.extra.tagMapping.deassigned futureInitial rootFuture
  have reserveFresh : GeneralBorrowTagMap.Fresh i.first.tree.tagMapping reserve := by
    rw [origin.firstTree]
    exact GeneralBorrowFreshMetadataChildAllocator.fresh_push s.entry.allocation.extra.tagMapping s.tracker.global.nextPointerTag reserve
      ⟨UInt32.ofNat s.entry.allocation.extra.tagMapping.mapping.size⟩ s.entry.allocation.extra.tagMapping.deassigned reserveInitial rootReserve
  have firstFuture : i.first.newTag≠future := by
    rw [origin.firstNewTag]
    intro same;have equal:=congrArg (fun tag : BorTag=>tag.value.toNat) same
    have before:=numerical.1
    omega
  have helperFuture : i.input.newTag≠future := by
    rw [i.tagEq,origin.tracker]
    intro same;have equal:=congrArg (fun tag : BorTag=>tag.value.toNat) same
    have before:=numerical.2.1
    omega
  have firstReserve : i.first.newTag≠reserve := by
    rw [origin.firstNewTag]
    intro same;have equal:=congrArg (fun tag : BorTag=>tag.value.toNat) same
    have before:=numerical.1
    omega
  have helperReserve : i.input.newTag≠reserve := by
    rw [i.tagEq,origin.tracker]
    intro same;have equal:=congrArg (fun tag : BorTag=>tag.value.toNat) same
    have before:=numerical.2.1
    omega
  have initialBounds : (0 : UInt64).toNat+s.len.toNat≤s.entry.allocation.extra.locations.size.bytes.toNat := by
    rw [s.full]
    simpa only [UInt64.toNat_zero,Nat.zero_add] using (Nat.le_refl s.len.toNat)
  have firstClean : GeneralBorrowGcVacantClean.VacantClean i.first.tree := by
    rw [origin.firstTree]
    exact GeneralBorrowPositiveWildcardPartitionVacantClean.preserves s.entry.allocation.extra s.tracker s.len s.initialState.well initialBounds s.vacantClean
  have helperNodes : i.input.tree.nodes.size=i.first.tree.nodes.size+1 := by
    rw [i.firstTreeEq]
    exact GeneralBorrowExposedScopedSharedSourceSize.child i.first i.firstTags i.selected i.head i.tail (fun _=>true) i.firstRaw i.firstAtBase i.firstFull
  have sourceState := GeneralBorrowPositiveWildcardPartitionFinalState.build s.entry.allocation.extra s.initialState s.tracker s.len
    (UInt64.pos_iff_ne_zero.mp s.positive) s.tagFresh s.noFree s.fits (by have room:=s.nodeRoom;omega) initialBounds
  have firstGrowth : i.first.tree.nodes.size≤s.entry.allocation.extra.nodes.size+1 := by
    rw [origin.firstTree]
    exact sourceState.2.2
  have room : i.input.tree.nodes.size+3<65536 := by
    have bound:=s.nodeRoom
    omega
  let helperRaw : GeneralBorrowExposedScopedSharedLeafConstructor.Resources i.input (held i).global.protectedTags i.selected i.head i.tail
      (GeneralBorrowFreshMixedChild.extend (fun _=>true) (index i.first).toNat) := by
    rw [←i.writableEq]
    exact i.raw
  have result := GeneralBorrowExposedScopedPostLenDefaultResources.prepare i.first i.input i.firstTags (held i).global i.id i.selected i.head i.tail
    i.firstRaw helperRaw i.firstAtBase i.firstFull i.atBase i.full i.firstTreeEq i.firstParentEq i.initialTags i.exprUnheld i.rangePositive
    firstClean future reserve futureFresh reserveFresh firstFuture helperFuture firstReserve helperReserve room
  exact result
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardPartitionAcceptedDefaultData
