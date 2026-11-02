import duplicate_prefix.GeneralBorrowPositiveWildcardAllCountInput
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardFamilyTags
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open GeneralBorrowPositiveWildcardFunctionState
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
abbrev expression (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (slotFresh : (next tracker fresh).global.nextPointerTag.value<18446744073709551615)
    (sharedFresh : (held tracker fresh slotFresh).global.nextPointerTag.value<18446744073709551615) :=
  ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) sharedFresh
abbrev ended (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (slotFresh : (next tracker fresh).global.nextPointerTag.value<18446744073709551615)
    (sharedFresh : (held tracker fresh slotFresh).global.nextPointerTag.value<18446744073709551615)
    (helperFresh : (expression tracker fresh slotFresh sharedFresh).global.nextPointerTag.value<18446744073709551615)
    (id : AllocId) : MachineHooks.BorrowState :=
  let expr:=expression tracker fresh slotFresh sharedFresh
  let registered:=TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker expr helperFresh) expr.global.nextPointerTag
  {registered with global:=registered.global.endCall (({} : FrameState).addProtector id expr.global.nextPointerTag)}
structure Plan (tracker : MachineHooks.BorrowState) (id : AllocId) where
  fresh : tracker.global.nextPointerTag.value<18446744073709551615
  slotFresh : (next tracker fresh).global.nextPointerTag.value<18446744073709551615
  sharedFresh : (held tracker fresh slotFresh).global.nextPointerTag.value<18446744073709551615
  helperFresh : (expression tracker fresh slotFresh sharedFresh).global.nextPointerTag.value<18446744073709551615
  mutableFresh : (ended tracker fresh slotFresh sharedFresh helperFresh id).global.nextPointerTag.value<18446744073709551615
  mutableHelperFresh : (ReferenceBorrowDriver.allocatedTracker (ended tracker fresh slotFresh sharedFresh helperFresh id) mutableFresh).global.nextPointerTag.value<18446744073709551615
  slotValue : (next tracker fresh).global.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+1
  sharedValue : (held tracker fresh slotFresh).global.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+2
  helperValue : (expression tracker fresh slotFresh sharedFresh).global.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+3
  mutableValue : (ended tracker fresh slotFresh sharedFresh helperFresh id).global.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+4
  mutableHelperValue : (ReferenceBorrowDriver.allocatedTracker (ended tracker fresh slotFresh sharedFresh helperFresh id) mutableFresh).global.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+5
/-- A single initial arithmetic reserve supplies all six actual invocation tags. -/
theorem make (tracker : MachineHooks.BorrowState) (id : AllocId)
    (room : tracker.global.nextPointerTag.value.toNat+6≤18446744073709551615) : Nonempty (Plan tracker id) := by
  have f0 : tracker.global.nextPointerTag.value<18446744073709551615 := UInt64.lt_iff_toNat_lt.mpr (by change _ < (18446744073709551615 : Nat); omega)
  have n1:=GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag f0
  change (next tracker f0).global.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+1 at n1
  have f1 : (next tracker f0).global.nextPointerTag.value<18446744073709551615 := UInt64.lt_iff_toNat_lt.mpr (by change _ < (18446744073709551615 : Nat); omega)
  have n2:=GenericFunctionEntryNumerics.successor_value (next tracker f0).global.nextPointerTag f1
  change (held tracker f0 f1).global.nextPointerTag.value.toNat=(next tracker f0).global.nextPointerTag.value.toNat+1 at n2
  have n2' : (held tracker f0 f1).global.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+2 := by omega
  have f2 : (held tracker f0 f1).global.nextPointerTag.value<18446744073709551615 := UInt64.lt_iff_toNat_lt.mpr (by change _ < (18446744073709551615 : Nat); omega)
  have n3:=GenericFunctionEntryNumerics.successor_value (held tracker f0 f1).global.nextPointerTag f2
  change (expression tracker f0 f1 f2).global.nextPointerTag.value.toNat=(held tracker f0 f1).global.nextPointerTag.value.toNat+1 at n3
  have n3' : (expression tracker f0 f1 f2).global.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+3 := by omega
  have f3 : (expression tracker f0 f1 f2).global.nextPointerTag.value<18446744073709551615 := UInt64.lt_iff_toNat_lt.mpr (by change _ < (18446744073709551615 : Nat); omega)
  have n4:=GenericFunctionEntryNumerics.successor_value (expression tracker f0 f1 f2).global.nextPointerTag f3
  change (ended tracker f0 f1 f2 f3 id).global.nextPointerTag.value.toNat=(expression tracker f0 f1 f2).global.nextPointerTag.value.toNat+1 at n4
  have n4' : (ended tracker f0 f1 f2 f3 id).global.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+4 := by omega
  have f4 : (ended tracker f0 f1 f2 f3 id).global.nextPointerTag.value<18446744073709551615 := UInt64.lt_iff_toNat_lt.mpr (by change _ < (18446744073709551615 : Nat); omega)
  have n5:=GenericFunctionEntryNumerics.successor_value (ended tracker f0 f1 f2 f3 id).global.nextPointerTag f4
  change (ReferenceBorrowDriver.allocatedTracker (ended tracker f0 f1 f2 f3 id) f4).global.nextPointerTag.value.toNat=(ended tracker f0 f1 f2 f3 id).global.nextPointerTag.value.toNat+1 at n5
  have n5' : (ReferenceBorrowDriver.allocatedTracker (ended tracker f0 f1 f2 f3 id) f4).global.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+5 := by omega
  have f5 : (ReferenceBorrowDriver.allocatedTracker (ended tracker f0 f1 f2 f3 id) f4).global.nextPointerTag.value<18446744073709551615 := UInt64.lt_iff_toNat_lt.mpr (by change _ < (18446744073709551615 : Nat); omega)
  exact ⟨⟨f0,f1,f2,f3,f4,f5,n1,n2',n3',n4',n5'⟩⟩
end DuplicatePrefix.GeneralBorrowPositiveWildcardFamilyTags
