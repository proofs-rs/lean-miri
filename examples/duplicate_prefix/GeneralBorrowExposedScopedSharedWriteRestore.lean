import duplicate_prefix.GeneralBorrowExposedScopedRestoredWriteData
import duplicate_prefix.GeneralBorrowFreshSharedPaths
namespace DuplicatePrefix.GeneralBorrowExposedScopedSharedWriteRestore
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Parent closure and actual two-child prefix metadata derive membership of
the older target in the post-helper hidden component. -/
theorem target_supported (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (child expr target selected head : UniIndex) (tail : List UniIndex) (support : Nat → Prop) (writable : Nat → Bool)
    (data : GeneralBorrowExposedScopedMixedRangeData.Data tree location protections child selected head tail support writable)
    (paths : (source_normal_projection tree location protections).topology.ancestorPath child.toNat=
      child.toNat::expr.toNat::(source_normal_projection tree location protections).topology.ancestorPath target.toNat) : support target.toNat := by
  have self:=GeneralBorrowFreshSharedPaths.ancestor_self (source_normal_projection tree location protections).topology target.toNat
  have member : target.toNat∈(source_normal_projection tree location protections).topology.ancestorPath child.toNat := by
    rw [paths]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ self)
  rw [←data.support_eq]
  exact GeneralBorrowPresence.ancestors_present _ data.base.component.support data.base.component.parents _ child.toNat data.base.component.anchor _ member

/-- Full target Write data is restored from the physical helper's released
mixed rows, actual singleton helper frame, and raw two-child path metadata.
RestoreTo, target support, helper hiddenness, and post-endCall cache coherence
are all derived internally. -/
noncomputable def restore (tree : BorrowTree) (location : LocationTree) (global : GlobalState)
    (allocation : AllocId) (child expr target selected head : UniIndex) (tail : List UniIndex) (support : Nat → Prop)
    (data : GeneralBorrowExposedScopedMixedRangeData.Data tree location global.protectedTags child selected head tail support (GeneralBorrowFreshSharedPrefix.labels expr child))
    (childContext : GeneralBorrowExposedKnownRootRangeData.Context tree child selected head tail)
    (targetNode exprNode childNode : TreeNode) (targetPresent : tree.nodeAt target=some targetNode)
    (exprPresent : tree.nodeAt expr=some exprNode) (childPresent : tree.nodeAt child=some childNode)
    (nodeTags : ∀ index value,tree.nodeAt index=some value → tree.indexOfTag value.tag=some index)
    (exprUnheld : global.protectedTags.contains exprNode.tag=false)
    (paths : ∀ location : LocationTree,(source_normal_projection tree location global.protectedTags).topology.ancestorPath child.toNat=
      child.toNat::expr.toNat::(source_normal_projection tree location global.protectedTags).topology.ancestorPath target.toNat)
    (exprOutside : ∀ location : LocationTree,expr.toNat∉(source_normal_projection tree location global.protectedTags).topology.ancestorPath target.toNat)
    (childOutside : ∀ location : LocationTree,child.toNat∉(source_normal_projection tree location global.protectedTags).topology.ancestorPath target.toNat)
    (short : tree.nodes.size<65536)
    (leaves : ∀ index,area.support index → ∃ node,tree.nodeAt index=some node ∧ node.children=#[] ∧ node.isExposed=true ∧
      GeneralBorrowWildcardVirtualLeaf.effective location index node=GeneralBorrowWildcardLeaf.unique)
    (first : head≠selected → area.support head) (rest : ∀ root∈tail,root≠selected → area.support root) :
    GeneralBorrowExposedKnownRootRangeData.Data tree location
      (global.endCall (({} : FrameState).addProtector allocation childNode.tag)).protectedTags target selected head tail .Write := by
  let frame:=({} : FrameState).addProtector allocation childNode.tag
  have restoration:=GeneralBorrowFreshSharedPrefix.restore_data tree global frame target expr child targetNode exprNode childNode
    targetPresent exprPresent childPresent allocation (by simp [frame,FrameState.addProtector]) exprUnheld paths exprOutside childOutside
  have supported:=target_supported tree location global.protectedTags child expr target selected head tail support _ data (paths location)
  let context : GeneralBorrowExposedKnownRootRangeData.Context tree target selected head tail:={
    childContext with anchorNode:=targetNode,anchorPresent:=targetPresent }
  have rootPath : ((source_normal_projection tree location global.protectedTags).topology.ancestorPath target.toNat).getLast!=selected.toNat := by
    have self:=GeneralBorrowFreshSharedPaths.ancestor_self (source_normal_projection tree location global.protectedTags).topology target.toNat
    have nonempty : (source_normal_projection tree location global.protectedTags).topology.ancestorPath target.toNat≠[] := by
      intro empty;rw [empty] at self;cases self
    have previous:=data.base.rootPath
    rw [paths location] at previous
    simpa only [List.getLast!_eq_getLast?_getD,List.getLast?_cons_of_ne_nil (List.cons_ne_nil _ _),List.getLast?_cons_of_ne_nil nonempty] using previous
  exact GeneralBorrowExposedScopedRestoredWriteData.restore tree location global allocation child target selected head tail support _ data context childNode childPresent nodeTags
    supported restoration rootPath short leaves first rest
end DuplicatePrefix.GeneralBorrowExposedScopedSharedWriteRestore
