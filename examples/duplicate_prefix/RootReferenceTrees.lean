import duplicate_prefix.RootReferenceInfo
import duplicate_prefix.ProtectedStages
namespace DuplicatePrefix.RootReferenceTrees
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows
open BorrowRangeAccess NestedConstruction RootReferenceInfo
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

def nextIndex (shared : Bool) : Fin 6 := if shared then 2 else 4
def count (shared : Bool) : Nat := if shared then 2 else 4
def initialTree (shared : Bool) (tags : Fin 6 → BorTag) (capacity offset len : UInt64) : BorrowTree :=
  if shared then tree2 tags (partitionWithInside capacity offset (offset+len) rootLocation (childLocation false))
  else tree4 tags (partitionWithInside capacity offset (offset+len) rootLocation (location4 true))
def finalTree (shared : Bool) (tags : Fin 6 → BorTag) (capacity offset len : UInt64) : BorrowTree :=
  if shared then tree3 tags (partitionWithInside capacity offset (offset+len) rootLocation (location3 false))
  else tree5 tags (partitionWithInside capacity offset (offset+len) rootLocation (location5 false))

theorem parent_read (shared : Bool) (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (protections : ProtectedTags) (mask : ProtectedStages.StageMask tags protections (count shared) false)
    (capacity offset len : UInt64) (positive : (0 : UInt64) < len)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat) :
    let tree := initialTree shared tags capacity offset len
    let result := tree.performBorrowAccessRange (.concrete (tags 1)) (Size.ofBytes offset) (Size.ofBytes len)
      .Read protections .VisitChildrenOfAccessed
    result.status = .Completed ∧ result.tree = tree := by
  cases shared with
  | false => exact ProtectedStages.parent_read4 tags distinct protections mask capacity offset len positive bounds
  | true => exact ProtectedStages.parent_read2 tags distinct protections mask capacity offset len positive bounds

theorem new_child (shared : Bool) (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (capacity offset len : UInt64) (positive : (0 : UInt64) < len)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat) :
    (initialTree shared tags capacity offset len).newChild (Size.ofBytes offset) (.concrete (tags 1)) (tags (nextIndex shared))
      (DedupRangeMap.new (Size.ofBytes len) (initial shared)) (policy shared).outsidePermission false =
      ⟨finalTree shared tags capacity offset len,.ok ()⟩ := by
  cases shared with
  | false => exact NestedConstruction.new_mutable4 tags distinct capacity offset len positive bounds
  | true => exact NestedConstruction.new_shared2 tags distinct capacity offset len positive bounds

#print axioms parent_read
#print axioms new_child
open Lean Elab Command in
run_cmd do
  for declaration in [``parent_read, ``new_child] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved axiom {dependency}"
end DuplicatePrefix.RootReferenceTrees
