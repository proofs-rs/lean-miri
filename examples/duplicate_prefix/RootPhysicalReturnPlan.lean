import duplicate_prefix.RootPhysicalReturnSupport
import duplicate_prefix.ProtectedRelease
import duplicate_prefix.EmptyBorrowHelpers
import duplicate_prefix.FourNodeRelease
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace DuplicatePrefix.RootPhysicalReturnPlan
open Miri.DataStructures
open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Input
open BorrowRangeAccess

inductive Profile (protections : ProtectedTags) : List (AllocId × BorTag) →
    MemoryState Provenance BorrowTree MiriMemoryKind → MemoryState Provenance BorrowTree MiriMemoryKind → Prop where
  | nil (memory) : Profile protections [] memory memory
  | nonlive (id tag info rows memory final)
      (lookup : memory.getAllocInfo id = .ok info) (notLive : info.kind ≠ .liveData)
      (tail : Profile protections rows memory final) : Profile protections ((id,tag)::rows) memory final
  | slot (id root child capacity written entry rows memory final)
      (present : memory.live.find? (fun row => row.1 == id) = some (id,entry))
      (tree : entry.allocation.extra = PhysicalMachineWrite.slotTree root child capacity written)
      (rootFree : protections.contains root = false) (childHeld : protections.contains child = true)
      (distinct : root ≠ child) (nonzero : capacity ≠ 0)
      (tail : Profile protections rows (StackPopRelease.commitTree memory id entry entry.allocation.extra) final) :
      Profile protections ((id,child)::rows) memory final
  | buffer (id root child capacity offset finish entry rows memory final)
      (present : memory.live.find? (fun row => row.1 == id) = some (id,entry))
      (tree : entry.allocation.extra = canonicalChildTree root child
        (partitionWithInside capacity offset finish rootLocation (childLocation false)))
      (rootFree : protections.contains root = false) (childHeld : protections.contains child = true)
      (distinct : root ≠ child)
      (tail : Profile protections rows (StackPopRelease.commitTree memory id entry entry.allocation.extra) final) :
      Profile protections ((id,child)::rows) memory final
  | emptyBuffer (id tags capacity entry rows memory final)
      (present : memory.live.find? (fun row => row.1 == id) = some (id,entry))
      (tree : entry.allocation.extra = NestedConstruction.tree2 tags (DedupRangeMap.new (Size.ofBytes capacity) rootLocation))
      (distinct : Function.Injective tags)
      (tail : Profile protections rows (StackPopRelease.commitTree memory id entry entry.allocation.extra) final) :
      Profile protections ((id,tags 1)::rows) memory final
  | nestedWritten (id tags capacity offset finish first second entry rows memory final)
      (present : memory.live.find? (fun row => row.1 == id) = some (id,entry))
      (tree : entry.allocation.extra = NestedBorrowAccess.nestedTree tags
        (MixedRangeMap.doubleSplit capacity offset finish first second rootLocation
          (NestedBorrowAccess.nestedLocation false) (NestedBorrowAccess.nestedLocation true) (NestedBorrowAccess.nestedLocation false)))
      (mask : ProtectedBorrowAccess.SixMask tags protections false) (distinct : Function.Injective tags)
      (tail : Profile protections rows (StackPopRelease.commitTree memory id entry entry.allocation.extra) final) :
      Profile protections ((id,tags 1)::rows) memory final
  | four (id tags capacity offset finish entry rows memory final)
      (present : memory.live.find? (fun row => row.1 == id)=some (id,entry))
      (tree : entry.allocation.extra = NestedConstruction.tree4 tags
        (partitionWithInside capacity offset finish rootLocation (NestedConstruction.location4 true)))
      (mask : ProtectedStages.StageMask tags protections 4 false) (distinct : Function.Injective tags)
      (tail : Profile protections rows (StackPopRelease.commitTree memory id entry entry.allocation.extra) final) :
      Profile protections ((id,tags 1)::rows) memory final
  | emptyFour (id tags capacity entry rows memory final)
      (present : memory.live.find? (fun row => row.1 == id)=some (id,entry))
      (tree : entry.allocation.extra = NestedConstruction.tree4 tags (DedupRangeMap.new (Size.ofBytes capacity) rootLocation))
      (distinct : Function.Injective tags)
      (tail : Profile protections rows (StackPopRelease.commitTree memory id entry entry.allocation.extra) final) :
      Profile protections ((id,tags 1)::rows) memory final

theorem to_plan {protections rows before after} (profile : Profile protections rows before after) :
    StackPopRelease.Plan protections rows before after := by
  induction profile with
  | nil memory => exact .nil _
  | nonlive id tag info rows memory final lookup nonlive tail ih => exact .skip _ _ _ _ _ _ lookup nonlive ih
  | slot id root child capacity written entry rows memory final present tree rootFree childHeld distinct nonzero tail ih =>
    apply StackPopRelease.Plan.live id child entry entry.allocation.extra rows memory final present
    · rw [tree]
      exact ReturnTreeAccess.slot_release root child capacity written protections rootFree childHeld distinct nonzero
    · exact ih
  | buffer id root child capacity offset finish entry rows memory final present tree rootFree childHeld distinct tail ih =>
    apply StackPopRelease.Plan.live id child entry entry.allocation.extra rows memory final present
    · rw [tree]
      exact ProtectedRelease.two_initial_release root child protections rootFree childHeld capacity offset finish distinct
    · exact ih
  | emptyBuffer id tags capacity entry rows memory final present tree distinct tail ih =>
    apply StackPopRelease.Plan.live id (tags 1) entry entry.allocation.extra rows memory final present
    · rw [tree]
      exact EmptyBorrowHelpers.outer2_release_zero tags distinct capacity protections
    · exact ih
  | nestedWritten id tags capacity offset finish first second entry rows memory final present tree mask distinct tail ih =>
    apply StackPopRelease.Plan.live id (tags 1) entry entry.allocation.extra rows memory final present
    · rw [tree]
      exact ProtectedRelease.outer_double_release tags protections mask capacity offset finish first second distinct
    · exact ih
  | four id tags capacity offset finish entry rows memory final present tree mask distinct tail ih =>
    apply StackPopRelease.Plan.live id (tags 1) entry entry.allocation.extra rows memory final present
    · rw [tree]
      exact FourNodeRelease.outer_initial_release tags protections mask capacity offset finish distinct
    · exact ih
  | emptyFour id tags capacity entry rows memory final present tree distinct tail ih =>
    apply StackPopRelease.Plan.live id (tags 1) entry entry.allocation.extra rows memory final present
    · rw [tree]
      exact EmptyBorrowHelpers.outer4_release_zero tags distinct capacity protections
    · exact ih

#print axioms to_plan
end DuplicatePrefix.RootPhysicalReturnPlan
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.RootPhysicalReturnPlan.to_plan) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved root release profile dependency {dependency}"
