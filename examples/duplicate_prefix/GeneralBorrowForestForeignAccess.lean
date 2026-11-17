import duplicate_prefix.GeneralBorrowWildcardSubtreeForeignIterator
import duplicate_prefix.GeneralBorrowForestAccessData

namespace DuplicatePrefix.GeneralBorrowForestForeignAccess
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess
open GeneralBorrowForestAccessData (Context)
open GeneralBorrowWildcardSubtreeRegion
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Stable initial records for any mode's actual normal-plus-extra-subtree
operation. Region exclusion is GRAPH-only, independent of current skip/SIFA
state; no visitor exclusion or successful traversal is an input. -/
structure LocationData (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor primary : UniIndex) (extras : List UniIndex) (kind : AccessKind) where
  forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology
  owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) anchor.toNat kind
  rootPath : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast! = primary.toNat
  region : Region tree location kind protections
  supported : ∀ root ∈ extras, region.support root
  foreignGraph : ∀ query, region.support query →
    query.toNat ∉ (source_normal_projection tree location protections).topology.ancestorPath anchor.toNat

/-- One REAL source operation completes and re-forms these initial records
for its own exact resulting location. Normal visitors may enter the foreign
region: their resulting ownership, rather than a skip-schedule premise,
derives the actual extra-subtree operations' input. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor primary : UniIndex) (extras : List UniIndex) (kind : AccessKind)
    (mode : ChildrenVisitMode) (range : ByteRange)
    (context : Context tree anchor primary extras)
    (data : LocationData tree location protections anchor primary extras kind)
    (fits : tree.nodes.data.size ≤ 4294967296) :
    source_access_status (source_tree_access_at tree location (some anchor) kind protections mode range) = none ∧
    Nonempty (LocationData tree
      (source_access_location (source_tree_access_at tree location (some anchor) kind protections mode range))
      protections anchor primary extras kind) := by
  obtain ⟨after,actual,status,preserved,cache,frame⟩ := GeneralBorrowWildcardSubtreeForeignIterator.access tree location protections
    anchor primary context.anchorNode context.primaryNode extras kind mode range data.forest data.owned context.depth context.children
    context.anchorPresent context.primaryPresent context.roots context.different data.rootPath data.region data.supported fits data.foreignGraph
    context.unexposed
  have normalOwner := GeneralBorrowRangePreserves.normal_location_owned tree location protections anchor kind mode fits data.forest data.owned
  have retained := GeneralBorrowForestRegionOwnerMerge.merge tree location
    (tree.performNormalAccessAt location anchor kind protections mode).location after protections
    anchor kind kind fits data.region normalOwner preserved frame data.foreignGraph
  refine ⟨status,?_⟩
  rw [actual]
  exact ⟨{
    forest := data.forest
    owned := retained
    rootPath := data.rootPath
    region := rebase data.region after preserved cache
    supported := data.supported
    foreignGraph := data.foreignGraph }⟩

/-- Use the exact resulting location as the next input, without re-assuming
permission, cache, graph or operation-success facts. Both modes are allowed at
each step; this record concerns one fixed tree before any constructor. -/
noncomputable def next (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor primary : UniIndex) (extras : List UniIndex) (kind : AccessKind)
    (mode : ChildrenVisitMode) (range : ByteRange)
    (context : Context tree anchor primary extras)
    (data : LocationData tree location protections anchor primary extras kind)
    (fits : tree.nodes.data.size ≤ 4294967296) :
    LocationData tree
      (source_access_location (source_tree_access_at tree location (some anchor) kind protections mode range))
      protections anchor primary extras kind :=
  Classical.choice (access tree location protections anchor primary extras kind mode range context data fits).2

end DuplicatePrefix.GeneralBorrowForestForeignAccess
