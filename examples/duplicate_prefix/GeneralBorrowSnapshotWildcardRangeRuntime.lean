import duplicate_prefix.GeneralBorrowSnapshotWildcardRangeBoth
import duplicate_prefix.DuplicatePrefixBorrowContract

namespace DuplicatePrefix.GeneralBorrowSnapshotWildcardRangeRuntime
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowSnapshotWildcardRangeBoth
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- Installing the actual ranged result reconstructs full runtime facts from
its preserved graph metadata and every physical result row. -/
theorem install (tree : BorrowTree) (global : GlobalState)
    (before : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (lower upper : UInt64) (result : BorrowTree.BorrowTreeAccessResult)
    (contract : Contract tree global.protectedTags lower upper result) :
    DuplicatePrefixBorrowContract.RuntimeFacts result.tree global := by
  have same : result.tree = {tree with locations := result.tree.locations} := by
    have nodes := contract.nodes
    have roots := contract.roots
    have tags := contract.tags
    cases tree
    cases result with
    | mk after visited status =>
      cases after
      simp_all
  have graph := GeneralBorrowStructuralHistoryState.graph_locations tree result.tree.locations before.formed.toGraphState
  rw [←same] at graph
  refine ⟨⟨⟨graph,contract.well⟩,?_⟩,?_,?_,?_⟩
  · intro position valid
    exact (contract.runtime position valid).profile
  · intro position valid
    exact (contract.runtime position valid).coherent
  · intro position valid
    exact (contract.runtime position valid).possible
  · refine ⟨?_,before.below.protectors⟩
    rw [contract.tags]
    exact before.below.mapping

/-- A bounded wildcard subrequest succeeds and retains both raw owner-window
permissions and the complete installed call-time runtime contract. -/
theorem access (tree : BorrowTree) (global : GlobalState)
    (before : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (offset len : Size) (kind : AccessKind) (mode : ChildrenVisitMode)
    (sliceStart sliceLen : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags none none none sliceStart sliceLen)
    (distinct : tree.roots.toList.Nodup) (short : tree.nodes.size < 65536)
    (requestLower : sliceStart.toNat ≤ offset.bytes.toNat)
    (requestStop : offset.bytes.toNat + len.bytes.toNat ≤ sliceStart.toNat + sliceLen.toNat) :
    let result := tree.performBorrowAccessRange .wildcard offset len kind global.protectedTags mode
    Contract tree global.protectedTags sliceStart (sliceStart + sliceLen) result ∧
      DuplicatePrefixBorrowContract.RuntimeFacts result.tree global := by
  have all : GeneralRangeMapState.Every (Runtime tree global.protectedTags) tree.locations := by
    intro position valid
    exact ⟨before.coherent position valid,before.formed.profile position valid,before.possible position valid⟩
  have contract := GeneralBorrowSnapshotWildcardRangeBoth.access tree global.protectedTags
    before.formed.toGraphState offset len kind mode sliceStart sliceLen positive distinct before.formed.well all
    short requestLower requestStop
  exact ⟨contract,install tree global before _ _ _ contract⟩

end DuplicatePrefix.GeneralBorrowSnapshotWildcardRangeRuntime
