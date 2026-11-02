import duplicate_prefix.GeneralBorrowForestMutableSlice
import duplicate_prefix.GeneralBorrowFreshActiveOnClean

namespace DuplicatePrefix.GeneralBorrowForestMutableClean
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralRangeMapState
open GeneralBorrowForestMutableAccess (Data)
open GeneralBorrowForestAccessData (Context)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- A physically vacant node index remains permission-Clean through the REAL
normal plus extra-root source operation. Support presence excludes it from all
wildcard visits; the normal visitor's vacant-slot frame is independently proved. -/
theorem local_clean (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor primary query : UniIndex) (extras : List UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode) (range : ByteRange)
    (context : Context tree anchor primary extras) (data : Data tree location protections anchor primary extras)
    (fits : tree.nodes.data.size ≤ 4294967296) (vacant : tree.nodes.get query = none) (clean : location.perms.get query = none) :
    (source_access_location (source_tree_access_at tree location (some anchor) kind protections mode range)).perms.get query = none := by
  let region := GeneralBorrowForestMutableAccess.region tree location protections anchor primary extras data kind
  have opOwner := GeneralBorrowRangePreserves.owned_for_access _ anchor.toNat kind .Write (by intro impossible;cases impossible) data.base.owned
  obtain ⟨after,actual,status,preserved,cache,frame⟩ := GeneralBorrowWildcardSubtreeForeignIterator.access tree location protections
    anchor primary context.anchorNode context.primaryNode extras kind mode range data.base.forest opOwner context.depth context.children
    context.anchorPresent context.primaryPresent context.roots context.different data.base.rootPath region data.base.supported fits data.base.foreignGraph
    context.unexposed
  have outside : ¬region.support query := by
    intro member
    obtain ⟨node,present⟩ := region.present query member
    rw [vacant] at present
    cases present
  rw [actual,frame query outside]
  exact GeneralBorrowFreshActiveOnClean.normal_vacant tree location protections anchor query kind mode context.depth context.children
    context.anchorNode context.anchorPresent vacant clean

end DuplicatePrefix.GeneralBorrowForestMutableClean
