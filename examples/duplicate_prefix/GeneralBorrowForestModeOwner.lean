import duplicate_prefix.GeneralBorrowForestModeAccess
import duplicate_prefix.GeneralBorrowForestRegionOwnerMerge
import duplicate_prefix.GeneralBorrowRangePreserves

namespace DuplicatePrefix.GeneralBorrowForestModeOwner
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess
open GeneralBorrowForestAccessData (Context)
open GeneralBorrowForestModeAccess (LocationData)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The real source operation retains the primary anchor's ownership after its
normal visit AND every actual extra-subtree visit. Supporting extra nodes are
foreign in the initial graph; their strong ForeignOwned contracts are retained
by the real subtree fold. Initial mutable ownership may be retained across Read.
All premises describe initial graph, permissions, counters and protections. -/
theorem access_owned (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor primary : UniIndex) (extras : List UniIndex) (kind ownerKind : AccessKind)
    (mode : ChildrenVisitMode) (range : ByteRange)
    (context : Context tree anchor primary extras)
    (data : LocationData tree location protections anchor primary extras kind mode)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (allowed : ownerKind = .Read → kind = .Read)
    (owner : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) anchor.toNat ownerKind)
    (foreignGraph : ∀ query, data.region.support query →
      query.toNat ∉ (source_normal_projection tree location protections).topology.ancestorPath anchor.toNat) :
    source_access_status (source_tree_access_at tree location (some anchor) kind protections mode range) = none ∧
    GeneralBorrowRange.LocationOwned tree protections anchor ownerKind
      (source_access_location (source_tree_access_at tree location (some anchor) kind protections mode range)) := by
  obtain ⟨after,actual,status,preserved,cache,frame⟩ := GeneralBorrowWildcardSubtreeModeIterator.access tree location protections
    anchor primary context.anchorNode context.primaryNode extras kind mode range data.forest data.owned context.depth context.children
    context.anchorPresent context.primaryPresent context.roots context.different data.rootPath data.region data.supported data.outside
    context.unexposed
  have normalOwner := GeneralBorrowRangePreserves.normal_location_owned_as tree location protections
    anchor kind ownerKind mode allowed fits data.forest owner
  have retained := GeneralBorrowForestRegionOwnerMerge.merge tree location
    (tree.performNormalAccessAt location anchor kind protections mode).location after protections
    anchor ownerKind kind fits data.region normalOwner preserved frame foreignGraph
  refine ⟨status,?_⟩
  rw [actual]
  exact ⟨⟨data.forest⟩,retained⟩

/-- In particular the ownership needed for the operation itself survives the
actual normal-plus-extra-subtree access, with either visitor mode. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor primary : UniIndex) (extras : List UniIndex) (kind : AccessKind)
    (mode : ChildrenVisitMode) (range : ByteRange)
    (context : Context tree anchor primary extras)
    (data : LocationData tree location protections anchor primary extras kind mode)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (foreignGraph : ∀ query, data.region.support query →
      query.toNat ∉ (source_normal_projection tree location protections).topology.ancestorPath anchor.toNat) :
    source_access_status (source_tree_access_at tree location (some anchor) kind protections mode range) = none ∧
    GeneralBorrowRange.LocationOwned tree protections anchor kind
      (source_access_location (source_tree_access_at tree location (some anchor) kind protections mode range)) :=
  access_owned tree location protections anchor primary extras kind kind mode range context data fits
    (fun same => same) data.owned foreignGraph

end DuplicatePrefix.GeneralBorrowForestModeOwner
