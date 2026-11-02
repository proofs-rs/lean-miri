import duplicate_prefix.GeneralBorrowPositiveWildcardWindowAcceptedNumerics
import duplicate_prefix.GeneralBorrowExposedScopedTwoWriteReadRestore
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardWindowAcceptedUnheld
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open GeneralBorrowPositiveWildcardWindowAcceptedInput GeneralBorrowPositiveWildcardWindowNonzeroInput
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

omit area in
theorem insert_absent (tags : ProtectedTags) (key query : BorTag) (kind : ProtectorKind)
    (different : query≠key) (absent : tags.contains query=false) :
    (tags.insert key kind).contains query=false :=
  (ProtectorInsertion.contains_other tags key query kind different).trans absent

omit area in
theorem end_absent (global : GlobalState) (frame : FrameState) (query : BorTag)
    (absent : global.protectedTags.contains query=false) : (global.endCall frame).protectedTags.contains query=false := by
  cases final : (global.endCall frame).protectedTags.contains query with
  | false => rfl
  | true => have prior:=GeneralBorrowRelease.end_call_weakens global frame query final;rw [absent] at prior;cases prior

abbrev mutableTracker (s : GeneralBorrowPositiveWildcardWindowAcceptedInput.Initial) :=
  ReferenceBorrowDriver.allocatedTracker (lenEnded s.toInitial) s.mutableFresh
abbrev mutableHeld (s : GeneralBorrowPositiveWildcardWindowAcceptedInput.Initial) :=
  TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker (mutableTracker s) s.mutableHelperFresh)
    (mutableTracker s).global.nextPointerTag
abbrev mutableEnded (s : GeneralBorrowPositiveWildcardWindowAcceptedInput.Initial) :=
  (mutableHeld s).endCall (({} : FrameState).addProtector s.id (mutableTracker s).global.nextPointerTag)

/-- Initial expression-tag absence survives the actual t0/t1/t3 insertions
and len-helper endCall. Only initial table absence and numeric tag distinctions
are used; unrelated global protector tags are unrestricted. -/
theorem after_len (s : GeneralBorrowPositiveWildcardWindowAcceptedInput.Initial) :
    (lenEnded s.toInitial).global.protectedTags.contains (mutableTag s.toInitial)=false := by
  let expr:=mutableTag s.toInitial
  let first:=s.tracker.global.nextPointerTag
  let slot:=(GeneralBorrowPositiveWildcardWindowFunctionState.next s.tracker s.fresh).global.nextPointerTag
  let helper:=helperTag s.toBase
  have numbers:=GeneralBorrowPositiveWildcardWindowAcceptedNumerics.values s
  have slotNat:=GenericFunctionEntryNumerics.successor_value s.tracker.global.nextPointerTag s.fresh
  change slot.value.toNat=first.value.toNat+1 at slotNat
  have exprNat : expr.value.toNat=first.value.toNat+4:=numbers.2.2.1
  have helperNat : helper.value.toNat=first.value.toNat+3:=numbers.2.1
  have firstDifferent : expr≠first := by intro equal;have same:=congrArg (fun tag : BorTag=>tag.value.toNat) equal;omega
  have slotDifferent : expr≠slot := by intro equal;have same:=congrArg (fun tag : BorTag=>tag.value.toNat) equal;omega
  have helperDifferent : expr≠helper := by intro equal;have same:=congrArg (fun tag : BorTag=>tag.value.toNat) equal;omega
  have heldFree : (held s.toBase).global.protectedTags.contains expr=false := by
    change ((s.tracker.global.protectedTags.insert first .StrongProtector).insert slot .StrongProtector).contains expr=false
    exact insert_absent _ slot expr _ slotDifferent (insert_absent _ first expr _ firstDifferent s.mutableUnheld)
  have lenFree : (lenHeld s.toInitial).global.protectedTags.contains expr=false := by
    change ((held s.toBase).global.protectedTags.insert helper .StrongProtector).contains expr=false
    exact insert_absent _ helper expr _ helperDifferent heldFree
  exact end_absent (lenHeld s.toInitial).global (({} : FrameState).addProtector s.id helper) expr lenFree

/-- Both real mutable escaping tags are absent after the actual as_mut_ptr
helper endCall. The source Initial already records t4 absence; actual distinct
insertions preserve it and singleton endCall removes t5. No global high-water
restriction or post-helper flag is added to the caller. -/
theorem after_mutable (s : GeneralBorrowPositiveWildcardWindowAcceptedInput.Initial) :
    (mutableEnded s).protectedTags.contains (mutableTag s.toInitial)=false ∧
      (mutableEnded s).protectedTags.contains (mutableTracker s).global.nextPointerTag=false := by
  have numbers:=GeneralBorrowPositiveWildcardWindowAcceptedNumerics.values s
  have different : mutableTag s.toInitial≠(mutableTracker s).global.nextPointerTag := by
    intro equal
    have same:=congrArg (fun tag : BorTag=>tag.value.toNat) equal
    have exprNat:=numbers.2.2.1
    have childNat:=numbers.2.2.2
    change (mutableTracker s).global.nextPointerTag.value.toNat=s.tracker.global.nextPointerTag.value.toNat+5 at childNat
    omega
  have free : (mutableHeld s).protectedTags.contains (mutableTag s.toInitial)=false := by
    change ((lenEnded s.toInitial).global.protectedTags.insert (mutableTracker s).global.nextPointerTag .StrongProtector).contains (mutableTag s.toInitial)=false
    exact insert_absent _ _ _ _ different (after_len s)
  exact GeneralBorrowExposedScopedTwoWriteReadRestore.ended_unheld (mutableHeld s) s.id
    (mutableTag s.toInitial) (mutableTracker s).global.nextPointerTag free
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardWindowAcceptedUnheld
