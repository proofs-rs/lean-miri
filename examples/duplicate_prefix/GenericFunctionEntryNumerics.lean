import duplicate_prefix.GenericFunctionEntrySharedBundle

namespace DuplicatePrefix.GenericFunctionEntryNumerics
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open GenericFunctionEntryState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false in
theorem range_positive (offset len capacity : UInt64) (positive : (0 : UInt64) < len)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat) : offset.toNat < (offset+len).toNat := by
  have fits : offset.toNat+len.toNat < 2^64 := by have limit := capacity.toNat_lt;omega
  have positiveNat : 0 < len.toNat := by simpa only [UInt64.lt_iff_toNat_lt,UInt64.toNat_zero] using positive
  rw [UInt64.toNat_add,Nat.mod_eq_of_lt fits]
  omega

set_option autoImplicit false in
theorem successor_value (tag : BorTag) (fresh : tag.value < 18446744073709551615) :
    (TypedRetagEmpty.successorTag tag fresh).value.toNat = tag.value.toNat+1 := by
  have bounded : tag.value.toNat < 18446744073709551615 := by simpa [UInt64.lt_iff_toNat_lt] using fresh
  have fits : tag.value.toNat+1 < 2^64 := by omega
  simp only [TypedRetagEmpty.successorTag,UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt fits]

set_option autoImplicit false in
/-- The expression tag cannot collide with either genuinely allocated ROOT tag;
its initial lack of a protector therefore survives both registrations. -/
theorem expression_unheld (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (fresh2 : (next tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (free : tracker.global.protectedTags.contains (held tracker fresh fresh2).global.nextPointerTag = false) :
    (held tracker fresh fresh2).global.protectedTags.contains (held tracker fresh fresh2).global.nextPointerTag = false := by
  have first := successor_value tracker.global.nextPointerTag fresh
  have second := successor_value (next tracker fresh).global.nextPointerTag fresh2
  change (next tracker fresh).global.nextPointerTag.value.toNat = tracker.global.nextPointerTag.value.toNat+1 at first
  change (held tracker fresh fresh2).global.nextPointerTag.value.toNat = (next tracker fresh).global.nextPointerTag.value.toNat+1 at second
  have different : (held tracker fresh fresh2).global.nextPointerTag ≠ tracker.global.nextPointerTag := by
    intro same
    have eq := congrArg (fun tag : BorTag => tag.value.toNat) same
    omega
  have different2 : (held tracker fresh fresh2).global.nextPointerTag ≠ (next tracker fresh).global.nextPointerTag := by
    intro same
    have eq := congrArg (fun tag : BorTag => tag.value.toNat) same
    omega
  exact buffer_root_free tracker fresh fresh2 _ different different2 free

set_option autoImplicit false in
theorem slot_lookup (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (buffer : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (parentTag : BorTag)
    (offset len : UInt64) (fresh2 : (next tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (slot : AllocId) (slotEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (slotRoot : BorTag)
    (updated : Allocation Provenance BorrowTree) :
    let entered := enteredMachine machine tracker fresh buffer entry parentTag offset len fresh2 slot slotEntry slotRoot updated
    (RootZeroCompleteState.tick options remaining span entered).memory.live.find? (fun row => row.1 == slot) =
      some (slot,{slotEntry with allocation := updated}) := by
  unfold RootZeroCompleteState.tick SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  exact MemoryCopyBridge.live_lookup_replaced _ slot _

set_option autoImplicit false in
theorem slot_child_held (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (fresh2 : (next tracker fresh).global.nextPointerTag.value < 18446744073709551615) :
    (held tracker fresh fresh2).global.protectedTags.contains (next tracker fresh).global.nextPointerTag = true := by
  simp only [held,TypedBorrowSteps.registeredTracker,TypedBorrowSteps.registeredGlobal]
  simp [ProtectedTags.contains]

set_option autoImplicit false in
/-- Three checked allocations supply all six distinctness facts for the four
initial/future tags. No pairwise-tag assumption is needed. -/
theorem four_tags_distinct (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (fresh2 : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (fresh3 : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) fresh2).global.nextPointerTag.value < 18446744073709551615) :
    let t1 := ReferenceBorrowDriver.allocatedTracker tracker fresh
    let t2 := ReferenceBorrowDriver.allocatedTracker t1 fresh2
    let t3 := ReferenceBorrowDriver.allocatedTracker t2 fresh3
    tracker.global.nextPointerTag ≠ t1.global.nextPointerTag ∧
      tracker.global.nextPointerTag ≠ t2.global.nextPointerTag ∧
      tracker.global.nextPointerTag ≠ t3.global.nextPointerTag ∧
      t1.global.nextPointerTag ≠ t2.global.nextPointerTag ∧
      t1.global.nextPointerTag ≠ t3.global.nextPointerTag ∧
      t2.global.nextPointerTag ≠ t3.global.nextPointerTag := by
  let t1 := ReferenceBorrowDriver.allocatedTracker tracker fresh
  let t2 := ReferenceBorrowDriver.allocatedTracker t1 fresh2
  let t3 := ReferenceBorrowDriver.allocatedTracker t2 fresh3
  have first := successor_value tracker.global.nextPointerTag fresh
  have second := successor_value t1.global.nextPointerTag fresh2
  have third := successor_value t2.global.nextPointerTag fresh3
  change t1.global.nextPointerTag.value.toNat = tracker.global.nextPointerTag.value.toNat+1 at first
  change t2.global.nextPointerTag.value.toNat = t1.global.nextPointerTag.value.toNat+1 at second
  change t3.global.nextPointerTag.value.toNat = t2.global.nextPointerTag.value.toNat+1 at third
  have ne (a b : BorTag) (less : a.value.toNat < b.value.toNat) : a ≠ b := by
    intro same
    have equal := congrArg (fun tag : BorTag => tag.value.toNat) same
    omega
  exact ⟨ne tracker.global.nextPointerTag t1.global.nextPointerTag (by omega),
    ne tracker.global.nextPointerTag t2.global.nextPointerTag (by omega),
    ne tracker.global.nextPointerTag t3.global.nextPointerTag (by omega),
    ne t1.global.nextPointerTag t2.global.nextPointerTag (by omega),
    ne t1.global.nextPointerTag t3.global.nextPointerTag (by omega),
    ne t2.global.nextPointerTag t3.global.nextPointerTag (by omega)⟩

end DuplicatePrefix.GenericFunctionEntryNumerics
