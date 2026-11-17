import duplicate_prefix.GeneralBorrowForestForeignAccess

namespace DuplicatePrefix.GeneralBorrowForestMutableAccess
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess
open GeneralBorrowForestAccessData (Context)
open GeneralBorrowWildcardSubtreeRegion
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Mutable source ownership plus BOTH kinds' raw zero counters on the common
foreign support. Write ownership alone does not imply Read-cache correctness. -/
structure Data (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor primary : UniIndex) (extras : List UniIndex) where
  base : GeneralBorrowForestForeignAccess.LocationData tree location protections anchor primary extras .Write
  readZero : ∀ index, base.region.support index → GeneralBorrowWildcardRelatednessBounds.count location.exposedCache index .Read = 0

def region (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor primary : UniIndex) (extras : List UniIndex)
    (data : Data tree location protections anchor primary extras) (kind : AccessKind) : Region tree location kind protections where
  support := data.base.region.support
  present := data.base.region.present
  children := data.base.region.children
  unexposed := data.base.region.unexposed
  zero := by cases kind with | Read => exact data.readZero | Write => exact data.base.region.zero
  owned := data.base.region.owned

/-- Actual normal-plus-extra-subtree Read OR Write retains mutable ownership
and re-forms BOTH counter-kind records. Initial support foreignness is a graph
property, independent of changing SIFA/skip schedules. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor primary : UniIndex) (extras : List UniIndex) (kind : AccessKind)
    (mode : ChildrenVisitMode) (range : ByteRange)
    (context : Context tree anchor primary extras)
    (data : Data tree location protections anchor primary extras)
    (fits : tree.nodes.data.size ≤ 4294967296) :
    source_access_status (source_tree_access_at tree location (some anchor) kind protections mode range) = none ∧
    Nonempty (Data tree (source_access_location (source_tree_access_at tree location (some anchor) kind protections mode range))
      protections anchor primary extras) := by
  let support := region tree location protections anchor primary extras data kind
  have opOwner := GeneralBorrowRangePreserves.owned_for_access _ anchor.toNat kind .Write (by intro impossible;cases impossible) data.base.owned
  obtain ⟨after,actual,status,preserved,cache,frame⟩ := GeneralBorrowWildcardSubtreeForeignIterator.access tree location protections
    anchor primary context.anchorNode context.primaryNode extras kind mode range data.base.forest opOwner context.depth context.children
    context.anchorPresent context.primaryPresent context.roots context.different data.base.rootPath support data.base.supported fits data.base.foreignGraph
    context.unexposed
  have normalOwner := GeneralBorrowRangePreserves.normal_location_owned_as tree location protections anchor kind .Write mode
    (by intro impossible;cases impossible) fits data.base.forest data.base.owned
  have retained := GeneralBorrowForestRegionOwnerMerge.merge tree location
    (tree.performNormalAccessAt location anchor kind protections mode).location after protections
    anchor .Write kind fits support normalOwner preserved frame data.base.foreignGraph
  refine ⟨status,?_⟩
  rw [actual]
  exact ⟨{
    base := {
      forest := data.base.forest
      owned := retained
      rootPath := data.base.rootPath
      region := rebase data.base.region after preserved cache
      supported := data.base.supported
      foreignGraph := data.base.foreignGraph }
    readZero := by intro index member;rw [cache];exact data.readZero index member }⟩

end DuplicatePrefix.GeneralBorrowForestMutableAccess
