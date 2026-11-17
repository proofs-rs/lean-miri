import duplicate_prefix.GeneralBorrowProtectedChildOrder
import duplicate_prefix.GeneralBorrowDefaultChildOrder
import duplicate_prefix.GeneralBorrowGcSurvivingRootPaths
import duplicate_prefix.GeneralBorrowGcNodeMetadata
import duplicate_prefix.GeneralBorrowRootExposureFrame
namespace DuplicatePrefix.GeneralBorrowParentTagInvariant
open Miri Miri.Memory Miri.ABI Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposure
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Permission, exposure, cache and allocator-map updates which retain node
storage cannot change parent/tag order. This requires no permission profile. -/
theorem nodes_frame (before after : BorrowTree) (same : after.nodes = before.nodes)
    (order : ParentTagOrder before) : ParentTagOrder after := by
  unfold ParentTagOrder
  rw [same]
  exact order

/-- Every stored parent is older than the actual allocator's fresh high-water tag.
Only raw runtime consistency is used, not successful borrowing or ownership. -/
theorem parent_below_fresh (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parent : UniIndex) (node : TreeNode) (present : tree.nodeAt parent = some node) :
    node.tag.value < global.nextPointerTag.value := by
  have bound := GeneralBorrowForestTagHighWater.mapped tree global.protectedTags global.nextPointerTag node.tag
    runtime.below parent (runtime.formed.allocator.nodeTags parent node present)
  exact UInt64.lt_iff_toNat_lt.mpr bound

theorem fresh (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) :
    GeneralBorrowTagMap.Fresh tree.tagMapping global.nextPointerTag := by
  intro row member equal
  have bound := runtime.below.mapping row member
  rw [equal] at bound
  exact Nat.lt_irrefl _ bound

/-- Actual protected mutable newChild, including sparse reuse and SIFA.
The parent/new-tag comparison is DERIVED from runtime high-water. -/
theorem protected_child (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (order : ParentTagOrder tree)
    (parentTag : BorTag) (parent : UniIndex) (node : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some node)
    (room : tree.nodes.size+1 ≤ 4294967295) (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    ParentTagOrder (GeneralBorrowFreshMetadataChildMutableSlot.result tree parentTag global.nextPointerTag offset len) :=
  GeneralBorrowProtectedChildOrder.construct tree global runtime order parentTag global.nextPointerTag parent node tagged present
    (fresh tree global runtime) room (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp (parent_below_fresh tree global runtime parent node present)))) offset len nonzero bounds

/-- Actual unprotected Default mutable newChild, including sparse reuse. -/
theorem default_child (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (order : ParentTagOrder tree)
    (parentTag : BorTag) (parent : UniIndex) (node : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some node)
    (room : tree.nodes.size+1 ≤ 4294967295) (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    ParentTagOrder (GeneralBorrowFreshMetadataChildDefaultSlot.result tree parentTag global.nextPointerTag offset len) :=
  GeneralBorrowDefaultChildOrder.construct tree global runtime order parentTag global.nextPointerTag parent node tagged present
    (fresh tree global runtime) room (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp (parent_below_fresh tree global runtime parent node present)))) offset len nonzero bounds

/-- Tag monotonicity along the finite, actual parent walk. -/
theorem walk_le (tree : BorrowTree) (order : ParentTagOrder tree) (depth : ParentDepth tree.nodes)
    (fuel : Nat) (source query : UniIndex) (node value : TreeNode)
    (present : tree.nodes.get source = some node) (found : tree.nodes.get query = some value)
    (member : query ∈ GeneralBorrowExposureAncestorFold.walk tree.nodes fuel source) :
    value.tag.value ≤ node.tag.value := by
  induction fuel generalizing source node with
  | zero => simp [GeneralBorrowExposureAncestorFold.walk] at member
  | succ fuel ih =>
    simp only [GeneralBorrowExposureAncestorFold.walk,present,List.mem_cons] at member
    rcases member with equal | tail
    · subst query
      cases Option.some.inj (present.symm.trans found)
      exact Nat.le_refl _
    · cases edge : node.parent with
      | none => simp [edge] at tail
      | some parent =>
        have tail' : query ∈ GeneralBorrowExposureAncestorFold.walk tree.nodes fuel parent := by simpa only [edge] using tail
        obtain ⟨parentNode,parentPresent,_⟩ := depth.parent source node present parent edge
        exact Nat.le_trans (ih parent parentNode parentPresent tail') (order source node present parent parentNode edge parentPresent)

/-- FULL actual GC contracts parent edges along original ancestry. Original
ordered tags therefore remain ordered after real deletion/unary collapse.
No successful GC, final graph certificate or post-state premise is supplied. -/
theorem collect (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (depth : ParentDepth tree.nodes) (closed : GeneralBorrowGraph.ChildNodes tree)
    (fits : tree.nodes.size ≤ 4294967296)
    (rootNodes : ∀ root ∈ tree.roots.toList,∃ node,tree.nodes.get root = some node ∧ node.parent = none)
    (well : tree.locations.WellFormed) (order : ParentTagOrder tree) (live : Array BorTag) :
    ParentTagOrder (tree.removeUnreachableTags live).tree := by
  obtain ⟨afterDepth,relation⟩ := GeneralBorrowGcSurvivingRootPaths.collect tree location protections forest depth closed fits rootNodes well live
  have metadata := GeneralBorrowGcNodeMetadata.collect tree live
  intro child node present parent parentNode edge parentPresent
  obtain ⟨old,oldPresent,oldFields⟩ := metadata child node present
  obtain ⟨oldParent,oldParentPresent,oldParentFields⟩ := metadata parent parentNode parentPresent
  have path : GeneralBorrowExposedNonleafPrimaryPath.Path (tree.removeUnreachableTags live).tree parent child :=
    .step (.refl parent parentNode parentPresent) node present edge
  have member := (relation child node present parent parentNode parentPresent).mp (path.walk afterDepth)
  have bound := walk_le tree order depth _ child parent old oldParent oldPresent oldParentPresent member
  simpa only [oldFields.tag,oldParentFields.tag] using bound
end DuplicatePrefix.GeneralBorrowParentTagInvariant
