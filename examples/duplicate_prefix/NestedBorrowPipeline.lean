import duplicate_prefix.ProtectedStages
import duplicate_prefix.ProtectedRelease

/-! An exact composition of source BorrowTree operations for the buffer's
helper reborrows. The four protection tables are supplied by the caller's
global retag/return steps; only the allocation's own node memberships matter.
This is a borrow-component summary, not a MIR call/return interpreter theorem. -/
namespace DuplicatePrefix.NestedBorrowPipeline
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows
open BorrowRangeAccess NestedBorrowAccess NestedConstruction ProtectedStages ProtectedBorrowAccess
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

structure Result where
  tree : BorrowTree
  accesses : Array BorrowTree.BorrowTreeAccessStatus
  insertions : Array (Except BorrowTree.ChildInsertError Unit)
  releases : Array BorrowTree.ProtectorReleaseStatus
  deriving DecidableEq, Repr

def prepare (tags : Fin 6 → BorTag) (capacity offset len : UInt64)
    (sharedProtected lenProtected mutableProtected helperProtected : ProtectedTags) : Result :=
  let initial := tree2 tags (partitionWithInside capacity offset (offset + len) rootLocation (childLocation false))
  let sharedRead := initial.performBorrowAccessRange (.concrete (tags 1))
    (Size.ofBytes offset) (Size.ofBytes len) .Read sharedProtected .VisitChildrenOfAccessed
  let shared := sharedRead.tree.newChild (Size.ofBytes offset) (.concrete (tags 1)) (tags 2)
    (DedupRangeMap.new (Size.ofBytes len) frozenRead) .Frozen false
  let lenRead := shared.tree.performBorrowAccessRange (.concrete (tags 2))
    (Size.ofBytes offset) (Size.ofBytes len) .Read lenProtected .VisitChildrenOfAccessed
  let lenChild := lenRead.tree.newChild (Size.ofBytes offset) (.concrete (tags 2)) (tags 3)
    (DedupRangeMap.new (Size.ofBytes len) frozenRead) .Frozen true
  let lenReturn := lenChild.tree.releaseProtector (tags 3) lenProtected
  let mutableRead := lenReturn.tree.performBorrowAccessRange (.concrete (tags 1))
    (Size.ofBytes offset) (Size.ofBytes len) .Read mutableProtected .VisitChildrenOfAccessed
  let mutableChild := mutableRead.tree.newChild (Size.ofBytes offset) (.concrete (tags 1)) (tags 4)
    (DedupRangeMap.new (Size.ofBytes len) NestedConstruction.mutableRead) (.ReservedFrz false) false
  let helperRead := mutableChild.tree.performBorrowAccessRange (.concrete (tags 4))
    (Size.ofBytes offset) (Size.ofBytes len) .Read helperProtected .VisitChildrenOfAccessed
  let helperChild := helperRead.tree.newChild (Size.ofBytes offset) (.concrete (tags 4)) (tags 5)
    (DedupRangeMap.new (Size.ofBytes len) mutableNone) (.ReservedFrz false) true
  let helperReturn := helperChild.tree.releaseProtector (tags 5) helperProtected
  { tree := helperReturn.tree
    accesses := #[sharedRead.status, lenRead.status, mutableRead.status, helperRead.status]
    insertions := #[shared.outcome, lenChild.outcome, mutableChild.outcome, helperChild.outcome]
    releases := #[lenReturn.status, helperReturn.status] }

theorem prepare_exact (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (capacity offset len : UInt64) (positive : (0 : UInt64) < len)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat)
    (sharedProtected lenProtected mutableProtected helperProtected : ProtectedTags)
    (sharedMask : StageMask tags sharedProtected 3 false)
    (lenMask : StageMask tags lenProtected 4 true)
    (mutableMask : StageMask tags mutableProtected 5 false)
    (helperMask : SixMask tags helperProtected true) :
    prepare tags capacity offset len sharedProtected lenProtected mutableProtected helperProtected =
      { tree := nestedTree tags (partitionWithInside capacity offset (offset + len) rootLocation (nestedLocation false))
        accesses := #[.Completed, .Completed, .Completed, .Completed]
        insertions := #[.ok (), .ok (), .ok (), .ok ()]
        releases := #[.Released, .Released] } := by
  have read2 := ProtectedStages.parent_read2 tags distinct sharedProtected
    (stage_mask_mono tags sharedProtected 2 3 false (by decide) sharedMask) capacity offset len positive bounds
  have child2 := new_shared2 tags distinct capacity offset len positive bounds
  have read3 := ProtectedStages.parent_read3 tags distinct lenProtected
    (len_mask_before_child tags lenProtected lenMask) capacity offset len false positive bounds
  have child3 := new_shared_entry3 tags distinct capacity offset len positive bounds
  have release3 := ProtectedStages.len_helper_release tags distinct lenProtected lenMask capacity offset (offset + len) false
  have read4 := ProtectedStages.parent_read4 tags distinct mutableProtected
    (stage_mask_mono tags mutableProtected 4 5 false (by decide) mutableMask) capacity offset len positive bounds
  have child4 := new_mutable4 tags distinct capacity offset len positive bounds
  have read5 := ProtectedStages.parent_read5 tags distinct helperProtected
    (six_mask_before_child tags helperProtected true helperMask) capacity offset len false positive bounds
  have child5 := new_mutable_entry5 tags distinct capacity offset len positive bounds
  have release5 := ProtectedRelease.helper6_initial_release tags helperProtected helperMask capacity offset (offset + len) distinct
  dsimp only at read2 read3 read4 read5 child2 child3 child4 child5 release3 release5
  simp only [prepare, read2.2, child2, read3.2, child3, release3, read4.2, child4, read5.2, child5, release5,
    read2.1, read3.1, read4.1, read5.1]

#print axioms prepare_exact
end DuplicatePrefix.NestedBorrowPipeline

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.NestedBorrowPipeline.prepare_exact) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "prepare_exact depends on unapproved axiom {dependency}"
