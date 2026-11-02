import duplicate_prefix.GeneralBorrowExposureMarkCardinality
import duplicate_prefix.GeneralBorrowExposureRelease
namespace DuplicatePrefix.GeneralBorrowGenericExposeCardinality
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowExposureCardinality
open DuplicatePrefix.GeneralBorrowExposureMarkGraph DuplicatePrefix.GeneralBorrowExposureRelease
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

def afterLocation (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) (index : UniIndex) (node : TreeNode) : LocationTree :=
  {location with exposedCache := (location.exposedCache.updateExposure (marked tree.nodes index node) index .None
    (effective location protections index node)).cache}

def afterTree (tree : BorrowTree) (capacity : UInt64) (location : LocationTree) (protections : ProtectedTags)
    (index : UniIndex) (node : TreeNode) : BorrowTree :=
  {tree with nodes := marked tree.nodes index node,locations := homogeneous capacity (afterLocation tree location protections index node)}

/-- Generic actual exposeTag contribution addition on one stored homogeneous
location, for any ParentDepth forest, effective permissions and protections.
Neither operation success nor a resulting cache is an input. -/
theorem expose (tree : BorrowTree) (capacity : UInt64) (location : LocationTree) (protections : ProtectedTags)
    (index : UniIndex) (node : TreeNode) (present : tree.nodeAt index = some node)
    (tagged : tree.indexOfTag node.tag = some index) (depth : ParentDepth tree.nodes)
    (unexposed : node.isExposed = false) (locations : tree.locations = homogeneous capacity location)
    (coherent : LocationCoherent tree location protections) :
    tree.exposeTag protections node.tag = ⟨afterTree tree capacity location protections index node,.ok ()⟩ ∧
    LocationCoherent (afterTree tree capacity location protections index node)
      (afterLocation tree location protections index node) protections := by
  have markedDepth := GeneralBorrowExposureMarkGraph.depth tree.nodes depth index node present
  have markedPresent : (marked tree.nodes index node).get index = some {node with isExposed := true} :=
    GeneralBorrowFreshLocation.get_same tree.nodes index _
  have success := update_exposure_succeeds location.exposedCache _ markedDepth index _ markedPresent .None
    (effective location protections index node)
  constructor
  · unfold BorrowTree.exposeTag
    simp only [tagged,present,unexposed,Bool.false_eq_true,↓reduceIte]
    unfold_source_update_locations
    simp only [Id.run,bind,pure,ForIn.forIn,locations,Std.Legacy.Range.forIn'_eq_forIn'_range',Std.Legacy.Range.size]
    simp only [show (homogeneous capacity location).entries.size = 1 from rfl,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
    simp only [show List.range' 0 1 = [0] from rfl,List.forIn'_cons,List.forIn'_nil,bind,pure]
    simp only [index_exact (homogeneous capacity location) 0 (by change 0<1;decide)]
    simp only [homogeneous,Array.getElem_singleton] at *
    erw [success]
    simp only [Except.mapError]
    erw [setAtPos_exact (homogeneous capacity location) 0 (by change 0<1;decide)]
    rfl
  · exact GeneralBorrowExposureMarkCardinality.preserves location.exposedCache tree.nodes depth
      (effective location protections) (GeneralBorrowExposureMarkCardinality.effective_stable location protections)
      coherent index node present unexposed
end DuplicatePrefix.GeneralBorrowGenericExposeCardinality
