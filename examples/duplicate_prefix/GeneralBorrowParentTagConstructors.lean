import duplicate_prefix.GeneralBorrowParentTagInvariant
import duplicate_prefix.GeneralBorrowSharedChildGraph
import duplicate_prefix.GeneralBorrowWildcardConstructorExact
namespace DuplicatePrefix.GeneralBorrowParentTagConstructors
open Miri Miri.Memory Miri.ABI Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposure
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
/-- The actual Frozen constructor, for either protector policy and arbitrary
coherent append/reuse slots. Fresh parent order is derived, not supplied. -/
theorem shared_child (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (order : ParentTagOrder tree)
    (parentTag : BorTag) (parent : UniIndex) (node : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some node)
    (room : tree.nodes.size+1 ≤ 4294967295) (held : Bool) (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    ParentTagOrder (tree.newChild (Size.ofBytes offset) (.concrete parentTag) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen held).tree := by
  let rank := GeneralBorrowStructuralHistoryShared.depth tree runtime.formed.toState
  have fresh := GeneralBorrowParentTagInvariant.fresh tree global runtime
  have freshOrder : node.tag.value ≤ global.nextPointerTag.value :=
    UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp (GeneralBorrowParentTagInvariant.parent_below_fresh tree global runtime parent node present)))
  cases GeneralBorrowStructuralHistoryShared.slot tree runtime.formed.toState parent node present room with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,global.nextPointerTag,parent,node,tagged,present,fresh,
        noFree,aligned,fits,held,offset,len,nonzero,runtime.formed.well,bounds⟩
    exact GeneralBorrowFreshParentTagOrder.staged_order tree rank order _ parent node _
      (GeneralBorrowFreshParentTagOrder.vacant_at_end tree _ (GeneralBorrowFreshMetadataChildShared.at_end input))
      present rfl freshOrder _ _ _ (GeneralBorrowFreshMetadataChildShared.shape input)
  | reuse child available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,global.nextPointerTag,parent,node,tagged,present,fresh,
        child,available,valid,vacant,slack,held,offset,len,nonzero,runtime.formed.well,bounds⟩
    exact GeneralBorrowFreshParentTagOrder.staged_order tree rank order child parent node _ vacant
      present rfl freshOrder _ _ _ (GeneralBorrowFreshMetadataChildSharedReuse.shape input)

/-- Adding an isolated parentless root at a vacant actual allocator index
preserves order of every existing edge. No comparison with old tags is needed. -/
theorem installed_root (tree : BorrowTree) (depth : ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (mapping : UniKeyMap BorTag) (index : UniIndex) (vacant : tree.nodes.get index = none)
    (tag : BorTag) (outside : Permission) (sifa : IdempotentForeignAccess) :
    ParentTagOrder (WildcardHitZeroConstructor.installed tree mapping index tag outside sifa) := by
  intro child node present parent parentNode edge parentPresent
  change (tree.nodes.insert index (WildcardHitZeroConstructor.rootNode tag outside sifa)).get child = some node at present
  change (tree.nodes.insert index (WildcardHitZeroConstructor.rootNode tag outside sifa)).get parent = some parentNode at parentPresent
  by_cases isNew : child = index
  · subst child
    rw [GeneralBorrowFreshLocation.get_same] at present
    cases present
    cases edge
  · rw [GeneralBorrowFreshLocation.get_other _ index child _ isNew] at present
    obtain ⟨oldParent,oldParentPresent,_⟩ := depth.parent child node present parent edge
    have different : parent ≠ index := by
      intro equal
      subst parent
      rw [vacant] at oldParentPresent
      cases oldParentPresent
    rw [GeneralBorrowFreshLocation.get_other _ index parent _ different] at parentPresent
    exact order child node present parent parentNode edge parentPresent

/-- Actual positive wildcard newChild preserves graph order for any legal
initial permission policy. Allocation selection and completion are derived. -/
theorem wildcard_child (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (order : ParentTagOrder tree)
    (room : tree.nodes.size+1 ≤ 4294967295)
    (outside : Permission) (sifa : IdempotentForeignAccess) (inside : LocationState) (held : Bool)
    (initial : outside.isInitial=true) (nonunique : outside.isUnique=false)
    (foreign : outside.strongestIdempotentForeignAccess held=.Access sifa)
    (insideInitial : inside.permission.isInitial=true)
    (insideForeign : inside.permission.strongestIdempotentForeignAccess held=.Access inside.idempotentForeignAccess)
    (offset len : UInt64) (nonzero : len≠0) (bounds : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat) :
    ParentTagOrder (tree.newChild (Size.ofBytes offset) .wildcard global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) inside) outside held).tree := by
  have fresh := GeneralBorrowParentTagInvariant.fresh tree global runtime
  obtain ⟨mapping,index,inserted,_,vacant,_⟩ := GeneralBorrowWildcardConstructorSlot.select tree global runtime global.nextPointerTag fresh room outside sifa
  rw [GeneralBorrowWildcardConstructorExact.exact tree runtime.formed.toState global.nextPointerTag fresh room mapping index inserted
    outside sifa inside held initial nonunique foreign insideInitial insideForeign offset len nonzero bounds]
  exact installed_root tree (GeneralBorrowStructuralHistoryShared.depth tree runtime.formed.toState) order mapping index vacant global.nextPointerTag outside sifa
end DuplicatePrefix.GeneralBorrowParentTagConstructors
