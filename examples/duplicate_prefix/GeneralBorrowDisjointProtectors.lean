import duplicate_prefix.GeneralBorrowSubsliceEntryData

namespace DuplicatePrefix.GeneralBorrowDisjointProtectors
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- A global protector map may be nonempty, while protecting no currently
present node of this allocation. It may protect nodes in other allocations. -/
def Unheld (tree : BorrowTree) (protections : ProtectedTags) : Prop :=
  ∀ row ∈ tree.nodes.entries, protections.contains row.2.tag = false

/-- A protector for any fresh tree tag gives a concrete nonempty instance of
this disjointness condition; no map-emptiness premise is hidden in Unheld. -/
theorem singleton_unheld (tree : BorrowTree) (tag : BorTag) (kind : ProtectorKind)
    (fresh : GeneralBorrowProtector.Fresh tree tag) : Unheld tree (({} : ProtectedTags).insert tag kind) := by
  intro row member
  rw [ProtectorInsertion.contains_other ({} : ProtectedTags) tag row.2.tag kind (fresh row member)]
  rfl

theorem singleton_nonempty (tag : BorTag) (kind : ProtectorKind) :
    (({} : ProtectedTags).insert tag kind).entries.size = 1 := by
  simp [ProtectedTags.insert]

/-- Unrelated global protectors change none of this tree's actual projected
normal-state data. No source access success or metadata equivalence is assumed. -/
theorem projection (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (unheld : Unheld tree protections) :
    source_normal_projection tree location protections = source_normal_projection tree location {} := by
  have projected : tree.nodes.entries.toList.filterMap
      (fun row => if protections.contains row.2.tag then some row.1.toNat else none) = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro row member
    rw [unheld row (by simpa only [Array.mem_def] using member)]
    rfl
  unfold_general_projection
  rw [projected]
  simp [ProtectedTags.contains,ProtectedTags.get]

/-- Form real arbitrary-subslice retag Data under a possibly nonempty global
protector map. The unprotected partition State is transported by the checked
source projection equation, not by a weakened access/protector rule. -/
noncomputable def data (tree : BorrowTree) (root : UniIndex) (bytes : UInt64)
    (state : GeneralBorrowPartitionState.State tree root bytes) (protections : ProtectedTags)
    (unheld : Unheld tree protections) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (offset len : UInt64) :
    GenericAsMutPtrEntryValidity.Data tree protections state.node.tag tag offset len := by
  let initial := GeneralBorrowSubsliceEntryData.data tree root bytes state tag fresh offset len
  exact {
    parent := initial.parent,root := initial.root,node := initial.node,depth := initial.depth
    children := initial.children,parentPresent := initial.parentPresent,roots := initial.roots,covered := initial.covered
    tagPresent := initial.tagPresent,tagFresh := initial.tagFresh,protectorFresh := initial.protectorFresh
    nodeFits := initial.nodeFits,slot := initial.slot,well := initial.well
    owned := by
      intro position valid positive start stop
      have previous := initial.owned position valid positive start stop
      unfold DuplicatePrefix.GeneralBorrowRange.LocationOwned
      rw [projection tree _ protections unheld]
      exact previous }

end DuplicatePrefix.GeneralBorrowDisjointProtectors
