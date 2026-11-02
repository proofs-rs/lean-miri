import duplicate_prefix.GeneralBorrowForestMutableAccess
import duplicate_prefix.GeneralBorrowWriteActivationUnique
import duplicate_prefix.GeneralBorrowFreshSharedPaths

namespace DuplicatePrefix.GeneralBorrowForestMutableUnique
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess
open GeneralBorrowForestMutableAccess (Data)
open GeneralBorrowForestAccessData (Context)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The REAL whole per-location source Write establishes stored Unique at its
selected non-Cell writable node. Extra-root visits complete and retain that
state because the common support is foreign to the selected node. No normal
or wildcard operation outcome is assumed. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor primary : UniIndex) (extras : List UniIndex) (mode : ChildrenVisitMode) (range : ByteRange)
    (context : Context tree anchor primary extras) (data : Data tree location protections anchor primary extras)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (notCell : ∀ state, (source_normal_projection tree location protections).stateAt anchor.toNat = some state → state.permission ≠ .Cell) :
    source_access_status (source_tree_access_at tree location (some anchor) .Write protections mode range) = none ∧
    ∃ state, (source_access_location (source_tree_access_at tree location (some anchor) .Write protections mode range)).perms.get anchor = some state ∧
      state.permission = .Unique := by
  let region := GeneralBorrowForestMutableAccess.region tree location protections anchor primary extras data .Write
  obtain ⟨after,actual,status,preserved,cache,frame⟩ := GeneralBorrowWildcardSubtreeForeignIterator.access tree location protections
    anchor primary context.anchorNode context.primaryNode extras .Write mode range data.base.forest data.base.owned context.depth context.children
    context.anchorPresent context.primaryPresent context.roots context.different data.base.rootPath region data.base.supported fits data.base.foreignGraph
    context.unexposed
  have outside : ¬region.support anchor := by
    intro member
    exact data.base.foreignGraph anchor member
      (GeneralBorrowFreshSharedPaths.ancestor_self (source_normal_projection tree location protections).topology anchor.toNat)
  obtain ⟨state,stored,unique⟩ := GeneralBorrowWriteActivationUnique.normal tree location protections anchor mode
    data.base.forest data.base.owned notCell
  refine ⟨status,state,?_,unique⟩
  rw [actual,frame anchor outside]
  exact stored

end DuplicatePrefix.GeneralBorrowForestMutableUnique
