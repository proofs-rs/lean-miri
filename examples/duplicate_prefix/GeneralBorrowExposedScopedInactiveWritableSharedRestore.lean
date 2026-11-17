import duplicate_prefix.GeneralBorrowExposedScopedSharedWriteRestore
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableReadEndCall
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSharedRestore
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

/-- Two source shared-child paths restore the older target under actual
singleton endCall. Writable old mixed/lazy leaves are retained by the real
protector deletion, with no exact-Unique or final-profile premise. -/
noncomputable def restore (tree : BorrowTree) (location : LocationTree) (global : GlobalState)
    (allocation : AllocId) (child expr target selected head : UniIndex) (tail : List UniIndex) (support : Nat→Prop)
    (data : GeneralBorrowExposedScopedInactiveWritableReadData.Data tree location global.protectedTags child selected head tail support
      (GeneralBorrowFreshSharedPrefix.labels expr child))
    (childContext : GeneralBorrowExposedKnownRootRangeData.Context tree child selected head tail)
    (targetNode exprNode childNode : TreeNode) (targetPresent : tree.nodeAt target=some targetNode)
    (exprPresent : tree.nodeAt expr=some exprNode) (childPresent : tree.nodeAt child=some childNode)
    (nodeTags : GeneralBorrowGcAllocator.NodeTags tree)
    (exprHidden : exprNode.isExposed=false) (childHidden : childNode.isExposed=false)
    (exprUnheld : global.protectedTags.contains exprNode.tag=false)
    (paths : ∀location : LocationTree,(source_normal_projection tree location global.protectedTags).topology.ancestorPath child.toNat=
      child.toNat::expr.toNat::(source_normal_projection tree location global.protectedTags).topology.ancestorPath target.toNat)
    (exprOutside : ∀location : LocationTree,expr.toNat∉(source_normal_projection tree location global.protectedTags).topology.ancestorPath target.toNat)
    (childOutside : ∀location : LocationTree,child.toNat∉(source_normal_projection tree location global.protectedTags).topology.ancestorPath target.toNat)
    (first : head≠selected→area.support head) (rest : ∀root∈tail,root≠selected→area.support root) :
    GeneralBorrowExposedScopedInactiveWritableReadData.Data tree location
      (global.endCall (({} : FrameState).addProtector allocation childNode.tag)).protectedTags target selected head tail support (fun _=>true) := by
  let frame:=({} : FrameState).addProtector allocation childNode.tag
  let after:=(global.endCall frame).protectedTags
  have hidden : ∀ query node,tree.nodeAt query=some node → node.tag=childNode.tag → node.isExposed=false := by
    intro query node present same
    have indices := (nodeTags query node present).symm.trans (same ▸ nodeTags child childNode childPresent)
    have equal := Option.some.inj indices
    subst query
    have nodes := Option.some.inj (present.symm.trans childPresent)
    subst node
    exact childHidden
  have ended:=GeneralBorrowExposedScopedInactiveWritableReadEndCall.end_call tree location global frame (by
    intro row member query node present same
    have equal : row=(allocation,childNode.tag) := by
      simpa only [frame,FrameState.addProtector,Array.toList_push,Array.toList_empty,List.nil_append,List.mem_singleton] using member
    subst row
    exact hidden query node present same) child selected head tail support _ childContext data
  have restoration:=GeneralBorrowFreshSharedPrefix.restore_data tree global frame target expr child targetNode exprNode childNode
    targetPresent exprPresent childPresent allocation (by simp [frame,FrameState.addProtector]) exprUnheld paths exprOutside childOutside
  have supported : support target.toNat := by
    have self:=GeneralBorrowFreshSharedPaths.ancestor_self (source_normal_projection tree location global.protectedTags).topology target.toNat
    have member : target.toNat∈(source_normal_projection tree location global.protectedTags).topology.ancestorPath child.toNat := by
      rw [paths location]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ self)
    rw [←data.base.support_eq]
    exact GeneralBorrowPresence.ancestors_present _ data.base.base.component.support data.base.base.component.parents _ child.toNat data.base.base.component.anchor _ member
  let context : GeneralBorrowExposedKnownRootRangeData.Context tree target selected head tail:={
    childContext with anchorNode:=targetNode,anchorPresent:=targetPresent}
  let component : GeneralBorrowExposedScopedNormal.Component (source_normal_projection tree location after).topology target.toNat:={
    support:=ended.base.base.component.support
    anchor:=by rw [ended.base.support_eq];exact supported
    parents:=ended.base.base.component.parents
    children:=ended.base.base.component.children}
  have mixed:=GeneralBorrowExposedScopedRestore.location tree location global.protectedTags after
    (GeneralBorrowRelease.end_call_weakens global frame) child target support _ restoration data.base.mixed
  have rootPath : ((source_normal_projection tree location after).topology.ancestorPath target.toNat).getLast!=selected.toNat := by
    have self:=GeneralBorrowFreshSharedPaths.ancestor_self (source_normal_projection tree location global.protectedTags).topology target.toNat
    have nonempty : (source_normal_projection tree location global.protectedTags).topology.ancestorPath target.toNat≠[] := by
      intro empty;rw [empty] at self;cases self
    have topologyEq : (source_normal_projection tree location after).topology=(source_normal_projection tree location global.protectedTags).topology := by
      unfold_general_projection
      rfl
    rw [topologyEq]
    have previous:=data.base.base.rootPath
    rw [paths location] at previous
    simpa only [List.getLast!_eq_getLast?_getD,List.getLast?_cons_of_ne_nil (List.cons_ne_nil _ _),List.getLast?_cons_of_ne_nil nonempty] using previous
  have ancestors : ∀ query node state,component.support query.toNat → tree.nodeAt query=some node → node.isExposed=true →
      tree.locationStateAt location query=some state →
      (query.toNat∈(source_normal_projection tree location after).topology.ancestorPath target.toNat ∧state.permission=.Unique) ∨
      (query.toNat∉(source_normal_projection tree location after).topology.ancestorPath target.toNat ∧state.permission=.Disabled) := by
    intro query node state included present exposed statePresent
    have notExpr : query≠expr := by
      intro equal;subst query
      have equalNode:=Option.some.inj (present.symm.trans exprPresent)
      subst node;rw [exprHidden] at exposed;cases exposed
    have notChild : query≠child := by
      intro equal;subst query
      have equalNode:=Option.some.inj (present.symm.trans childPresent)
      subst node;rw [childHidden] at exposed;cases exposed
    have topologyEq : (source_normal_projection tree location after).topology=(source_normal_projection tree location global.protectedTags).topology := by
      unfold_general_projection
      rfl
    have originalIncluded : data.base.base.component.support query.toNat := by
      rw [data.base.support_eq]
      rw [←ended.base.support_eq]
      exact included
    have previous:=data.base.base.ancestors query node state originalIncluded present exposed statePresent
    rw [paths location] at previous
    rw [topologyEq]
    rcases previous with good|bad
    · exact Or.inl ⟨by
        have member:=good.1
        simp only [List.mem_cons] at member
        rcases member with equal|equal|member
        · exact False.elim (notChild (GeneralBorrowNodeUpdate.index_injective _ _ equal))
        · exact False.elim (notExpr (GeneralBorrowNodeUpdate.index_injective _ _ equal))
        · exact member,good.2⟩
    · exact Or.inr ⟨fun member=>bad.1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)),bad.2⟩
  let base:=GeneralBorrowExposedScopedInactiveLeafSeed.seed tree location after target selected head tail support (fun _=>true) context
    ended.base.base.forest component ended.base.support_eq mixed rootPath ancestors ended.base.base.separate
    ended.base.base.coherent ended.short (by
      intro query included
      obtain ⟨node,present,leaf,exposed⟩:=ended.leaves query included
      have good:=ended.writableLeaves query node included present
      exact ⟨node,present,leaf,exposed,GeneralBorrowSparseExposedLeafState.supports _ _ good .Read,good.1⟩) first rest
  exact ⟨⟨base,ended.base.support_eq,mixed⟩,ended.short,ended.leaves,ended.writableLeaves⟩
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSharedRestore
