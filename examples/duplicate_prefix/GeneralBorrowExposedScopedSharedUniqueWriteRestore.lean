import duplicate_prefix.GeneralBorrowExposedScopedSharedWriteRestore
import duplicate_prefix.GeneralBorrowExposedScopedUniqueReadData
namespace DuplicatePrefix.GeneralBorrowExposedScopedSharedUniqueWriteRestore
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- The exact Unique rows retained by the source helper Read/release provide
all foreign Write profiles; the physical helper postdata needs no Write-ready
or per-root successful-call assumption. -/
noncomputable def restore (tree : BorrowTree) (location : LocationTree) (global : GlobalState)
    (allocation : AllocId) (child expr target selected head : UniIndex) (tail : List UniIndex) (support : Nat → Prop)
    (data : GeneralBorrowExposedScopedUniqueReadData.Data tree location global.protectedTags child selected head tail support (GeneralBorrowFreshSharedPrefix.labels expr child))
    (childContext : GeneralBorrowExposedKnownRootRangeData.Context tree child selected head tail)
    (targetNode exprNode childNode : TreeNode) (targetPresent : tree.nodeAt target=some targetNode)
    (exprPresent : tree.nodeAt expr=some exprNode) (childPresent : tree.nodeAt child=some childNode)
    (nodeTags : ∀ index value,tree.nodeAt index=some value → tree.indexOfTag value.tag=some index)
    (exprUnheld : global.protectedTags.contains exprNode.tag=false)
    (paths : ∀ location : LocationTree,(source_normal_projection tree location global.protectedTags).topology.ancestorPath child.toNat=
      child.toNat::expr.toNat::(source_normal_projection tree location global.protectedTags).topology.ancestorPath target.toNat)
    (exprOutside : ∀ location : LocationTree,expr.toNat∉(source_normal_projection tree location global.protectedTags).topology.ancestorPath target.toNat)
    (childOutside : ∀ location : LocationTree,child.toNat∉(source_normal_projection tree location global.protectedTags).topology.ancestorPath target.toNat)
    (first : head≠selected → area.support head) (rest : ∀ root∈tail,root≠selected → area.support root) :
    GeneralBorrowExposedKnownRootRangeData.Data tree location
      (global.endCall (({} : FrameState).addProtector allocation childNode.tag)).protectedTags target selected head tail .Write := by
  apply GeneralBorrowExposedScopedSharedWriteRestore.restore tree location global allocation child expr target selected head tail support data.base childContext
    targetNode exprNode childNode targetPresent exprPresent childPresent nodeTags exprUnheld paths exprOutside childOutside data.short
  · intro index included
    obtain ⟨node,present,leaf,exposed⟩:=data.leaves index included
    refine ⟨node,present,leaf,exposed,?_⟩
    simp only [GeneralBorrowWildcardVirtualLeaf.effective,data.unique index included,Option.getD_some]
  · exact first
  · exact rest

/-- Restore the entire actually released helper range, preserving source
range partitions and using the actual ended helper table at every location. -/
theorem ranged (tree : BorrowTree) (global : GlobalState) (allocation : AllocId)
    (child expr target selected head : UniIndex) (tail : List UniIndex) (support : Nat → Prop) (lower upper : UInt64)
    (owned : GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty
      (GeneralBorrowExposedScopedUniqueReadData.Data tree location global.protectedTags child selected head tail support (GeneralBorrowFreshSharedPrefix.labels expr child))) lower upper tree.locations)
    (childContext : GeneralBorrowExposedKnownRootRangeData.Context tree child selected head tail)
    (targetNode exprNode childNode : TreeNode) (targetPresent : tree.nodeAt target=some targetNode)
    (exprPresent : tree.nodeAt expr=some exprNode) (childPresent : tree.nodeAt child=some childNode)
    (nodeTags : ∀ index value,tree.nodeAt index=some value → tree.indexOfTag value.tag=some index)
    (exprUnheld : global.protectedTags.contains exprNode.tag=false)
    (paths : ∀ location : LocationTree,(source_normal_projection tree location global.protectedTags).topology.ancestorPath child.toNat=
      child.toNat::expr.toNat::(source_normal_projection tree location global.protectedTags).topology.ancestorPath target.toNat)
    (exprOutside : ∀ location : LocationTree,expr.toNat∉(source_normal_projection tree location global.protectedTags).topology.ancestorPath target.toNat)
    (childOutside : ∀ location : LocationTree,child.toNat∉(source_normal_projection tree location global.protectedTags).topology.ancestorPath target.toNat)
    (first : head≠selected → area.support head) (rest : ∀ root∈tail,root≠selected → area.support root) :
    GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty
      (GeneralBorrowExposedKnownRootRangeData.Data tree location
        (global.endCall (({} : FrameState).addProtector allocation childNode.tag)).protectedTags target selected head tail .Write)) lower upper tree.locations := by
  intro position valid positive start stop
  obtain ⟨data⟩:=owned position valid positive start stop
  exact ⟨restore tree _ global allocation child expr target selected head tail support data childContext targetNode exprNode childNode
    targetPresent exprPresent childPresent nodeTags exprUnheld paths exprOutside childOutside first rest⟩
end DuplicatePrefix.GeneralBorrowExposedScopedSharedUniqueWriteRestore
