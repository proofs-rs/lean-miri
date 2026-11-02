import duplicate_prefix.DuplicatePrefixBorrowContract
import duplicate_prefix.ProvenanceCopy
import duplicate_prefix.GeneralBorrowWildcardParentTagOrder

namespace DuplicatePrefix.DuplicatePrefixRuntimeInput
open Miri Miri.Memory Miri.TreeBorrows Miri.Interpreter

set_option autoImplicit false in
/-- Initial-state invariant candidate, separate from slice ownership and
numeric headroom. Every live allocation has a real formed forest/partition,
coherent exposure cache, possible scalar states and structurally valid byte
storage. Root uniqueness is explicit: roots are iterated, not deduplicated by
the interpreter. No execution history or operation success is a field.
The candidate's necessity and preservation are separate proof obligations. -/
structure State {K U : Type} (before : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (tracker : MachineHooks.BorrowState) : Prop where
  enabled : before.borrowTracker = some tracker
  allocationIds : (before.memory.live.toList.map Prod.fst).Nodup
  cachedRootIds : (tracker.global.rootPointerTags.toList.map Prod.fst).Nodup
  cachedRootTags : (tracker.global.rootPointerTags.toList.map Prod.snd).Nodup
  tags : (before.memory.live.toList.flatMap fun row =>
    row.2.allocation.extra.tagMapping.mapping.toList.map Prod.fst).Nodup
  formed : ∀ row ∈ before.memory.live.toList,
    GeneralBorrowStructuralHistorySifaState.Formed row.2.allocation.extra tracker.global.protectedTags
  roots : ∀ row ∈ before.memory.live.toList, row.2.allocation.extra.roots.toList.Nodup
  coherent : ∀ row ∈ before.memory.live.toList,
    GeneralRangeMapState.Every (fun location =>
      GeneralBorrowExposureCardinality.LocationCoherent row.2.allocation.extra location tracker.global.protectedTags)
      row.2.allocation.extra.locations
  possible : ∀ row ∈ before.memory.live.toList,
    GeneralRangeMapState.Every (fun location => ∀ index node,
      row.2.allocation.extra.nodeAt index = some node →
      ((location.perms.get index).getD node.defaultLocationState).possible = true)
      row.2.allocation.extra.locations
  byteLength : ∀ row ∈ before.memory.live.toList,
    row.2.allocation.len = row.2.allocation.byteSize.bytes.toNat
  maskValid : ∀ row ∈ before.memory.live.toList,
    InitMaskCopy.WellFormed row.2.allocation.initializationMask
  maskLength : ∀ row ∈ before.memory.live.toList,
    row.2.allocation.initializationMask.len = row.2.allocation.byteSize
  provenance : ∀ row ∈ before.memory.live.toList,
    ProvenanceCopy.WellFormed row.2.allocation.provenanceMap row.2.allocation.len
  treeLength : ∀ row ∈ before.memory.live.toList,
    row.2.allocation.extra.locations.size = row.2.allocation.byteSize

set_option autoImplicit false in
/-- Explicitly strengthened call-time state condition, requested by the user.
The original State remains available unchanged. Parent tags may not exceed
child tags in any live tree. This is static input data, not operation success,
NoUB, an axiom, or a claim that every valid execution supplies this condition.
Ordinary-valid-state coverage and preservation remain separate obligations. -/
structure OrderedState {K U : Type}
    (before : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (tracker : MachineHooks.BorrowState) extends State before tracker : Prop where
  parentTags : ∀ row ∈ before.memory.live.toList,
    GeneralBorrowWildcardParentTagOrder.ParentTagOrder row.2.allocation.extra

/-- The strengthened initial condition supplies the selected live tree's
order directly, without a formation/history certificate. -/
theorem OrderedState.parent_order {K U : Type}
    {before : MachineHooks.MachineState K (ValidityMachine.UserState U)}
    {tracker : MachineHooks.BorrowState} (runtime : OrderedState before tracker)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (present : before.memory.live.find? (fun row => row.1 == id) = some (id,entry)) :
    GeneralBorrowWildcardParentTagOrder.ParentTagOrder entry.allocation.extra :=
  runtime.parentTags (id,entry) (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some present))

/-- Vacant permission Clean follows from the explicit Formed/SIFA invariant;
free-slot accounting or graph well-formedness alone is never substituted. -/
theorem vacant_clean {K U : Type}
    {before : MachineHooks.MachineState K (ValidityMachine.UserState U)}
    {tracker : MachineHooks.BorrowState} (runtime : State before tracker)
    (row : AllocId × LocalAllocation Provenance BorrowTree K) (live : row ∈ before.memory.live.toList) :
    GeneralBorrowGcVacantClean.VacantClean row.2.allocation.extra :=
  GeneralBorrowStructuralHistorySifaState.vacant_clean _ _ (runtime.formed row live)

end DuplicatePrefix.DuplicatePrefixRuntimeInput
