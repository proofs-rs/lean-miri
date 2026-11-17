import duplicate_prefix.GeneralBorrowForestForeignSlice
import duplicate_prefix.GeneralBorrowFreshActiveOnClean

namespace DuplicatePrefix.GeneralBorrowForestForeignClean
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralRangeMapState
open GeneralBorrowForestForeignAccess (LocationData)
open GeneralBorrowForestAccessData (Context)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- A physically vacant node index remains permission-Clean through the REAL
normal plus extra-root source operation. Support presence excludes it from all
wildcard visits; the normal visitor's vacant-slot frame is independently proved. -/
theorem local_clean (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor primary query : UniIndex) (extras : List UniIndex) (mode : ChildrenVisitMode) (range : ByteRange)
    (context : Context tree anchor primary extras) (data : LocationData tree location protections anchor primary extras .Read)
    (fits : tree.nodes.data.size ≤ 4294967296) (vacant : tree.nodes.get query = none) (clean : location.perms.get query = none) :
    (source_access_location (source_tree_access_at tree location (some anchor) .Read protections mode range)).perms.get query = none := by
  let region := data.region
  have opOwner := data.owned
  obtain ⟨after,actual,status,preserved,cache,frame⟩ := GeneralBorrowWildcardSubtreeForeignIterator.access tree location protections
    anchor primary context.anchorNode context.primaryNode extras .Read mode range data.forest opOwner context.depth context.children
    context.anchorPresent context.primaryPresent context.roots context.different data.rootPath region data.supported fits data.foreignGraph
    context.unexposed
  have outside : ¬region.support query := by
    intro member
    obtain ⟨node,present⟩ := region.present query member
    rw [vacant] at present
    cases present
  rw [actual,frame query outside]
  exact GeneralBorrowFreshActiveOnClean.normal_vacant tree location protections anchor query .Read mode context.depth context.children
    context.anchorNode context.anchorPresent vacant clean

end DuplicatePrefix.GeneralBorrowForestForeignClean
