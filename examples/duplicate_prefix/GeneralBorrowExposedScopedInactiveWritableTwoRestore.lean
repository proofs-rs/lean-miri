import duplicate_prefix.GeneralBorrowFreshRestoreData
import duplicate_prefix.GeneralBorrowExposedScopedSharedWriteRestore
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableReadEndCall
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableTwoRestore
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

/-- Two unprotected escaping child paths restore the original target while
retaining its exposed Unique/Disabled profile and mixed writable old leaves. -/
noncomputable def restore (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (child expr target selected head : UniIndex) (tail : List UniIndex) (support : Nat→Prop)
    (data : GeneralBorrowExposedScopedInactiveWritableReadData.Data tree location protections child selected head tail support (fun _=>true))
    (childContext : GeneralBorrowExposedKnownRootRangeData.Context tree child selected head tail)
    (targetNode exprNode childNode : TreeNode) (targetPresent : tree.nodeAt target=some targetNode)
    (exprPresent : tree.nodeAt expr=some exprNode) (childPresent : tree.nodeAt child=some childNode)
    (exprHidden : exprNode.isExposed=false) (childHidden : childNode.isExposed=false)
    (exprUnheld : protections.contains exprNode.tag=false)
    (childUnheld : protections.contains childNode.tag=false)
    (paths : ∀location : LocationTree,(source_normal_projection tree location protections).topology.ancestorPath child.toNat=
      child.toNat::expr.toNat::(source_normal_projection tree location protections).topology.ancestorPath target.toNat)
    (first : head≠selected→area.support head) (rest : ∀root∈tail,root≠selected→area.support root) :
    GeneralBorrowExposedScopedInactiveWritableReadData.Data tree location
      protections target selected head tail support (fun _=>true) := by
  have subset (row : LocationTree) (position : Nat)
      (member : position∈(source_normal_projection tree row protections).topology.ancestorPath target.toNat) :
      position∈(source_normal_projection tree row protections).topology.ancestorPath child.toNat := by
    rw [paths row]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)
  have restoration := GeneralBorrowFreshRestoreData.from_paths tree protections protections child target targetNode targetPresent subset (by
    intro row index node present localChild foreignTarget
    rw [paths row] at localChild
    rcases List.mem_cons.mp localChild with equal | member
    · have same : index=child := GeneralBorrowNodeUpdate.index_injective index child equal
      subst index
      have nodeEq : node=childNode := Option.some.inj (present.symm.trans childPresent)
      subst node
      exact childUnheld
    · rcases List.mem_cons.mp member with equal | member
      · have same : index=expr := GeneralBorrowNodeUpdate.index_injective index expr equal
        subst index
        have nodeEq : node=exprNode := Option.some.inj (present.symm.trans exprPresent)
        subst node
        exact exprUnheld
      · exact False.elim (foreignTarget member))
  have supported : support target.toNat := by
    have self:=GeneralBorrowFreshSharedPaths.ancestor_self (source_normal_projection tree location protections).topology target.toNat
    have member : target.toNat∈(source_normal_projection tree location protections).topology.ancestorPath child.toNat := by
      rw [paths location]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ self)
    rw [←data.base.support_eq]
    exact GeneralBorrowPresence.ancestors_present _ data.base.base.component.support data.base.base.component.parents _ child.toNat data.base.base.component.anchor _ member
  let context : GeneralBorrowExposedKnownRootRangeData.Context tree target selected head tail:={
    childContext with anchorNode:=targetNode,anchorPresent:=targetPresent}
  let component : GeneralBorrowExposedScopedNormal.Component (source_normal_projection tree location protections).topology target.toNat:={
    support:=data.base.base.component.support
    anchor:=by rw [data.base.support_eq];exact supported
    parents:=data.base.base.component.parents
    children:=data.base.base.component.children}
  have mixed:=GeneralBorrowExposedScopedRestore.location tree location protections protections
    (fun _ held=>held) child target support _ restoration data.base.mixed
  have rootPath : ((source_normal_projection tree location protections).topology.ancestorPath target.toNat).getLast!=selected.toNat := by
    have self:=GeneralBorrowFreshSharedPaths.ancestor_self (source_normal_projection tree location protections).topology target.toNat
    have nonempty : (source_normal_projection tree location protections).topology.ancestorPath target.toNat≠[] := by
      intro empty;rw [empty] at self;cases self
    have previous:=data.base.base.rootPath
    rw [paths location] at previous
    simpa only [List.getLast!_eq_getLast?_getD,List.getLast?_cons_of_ne_nil (List.cons_ne_nil _ _),List.getLast?_cons_of_ne_nil nonempty] using previous
  have ancestors : ∀ query node state,component.support query.toNat → tree.nodeAt query=some node → node.isExposed=true →
      tree.locationStateAt location query=some state →
      (query.toNat∈(source_normal_projection tree location protections).topology.ancestorPath target.toNat ∧state.permission=.Unique) ∨
      (query.toNat∉(source_normal_projection tree location protections).topology.ancestorPath target.toNat ∧state.permission=.Disabled) := by
    intro query node state included present exposed statePresent
    have notExpr : query≠expr := by
      intro equal;subst query
      have equalNode:=Option.some.inj (present.symm.trans exprPresent)
      subst node;rw [exprHidden] at exposed;cases exposed
    have notChild : query≠child := by
      intro equal;subst query
      have equalNode:=Option.some.inj (present.symm.trans childPresent)
      subst node;rw [childHidden] at exposed;cases exposed
    have originalIncluded : data.base.base.component.support query.toNat := included
    have previous:=data.base.base.ancestors query node state originalIncluded present exposed statePresent
    rw [paths location] at previous
    rcases previous with good|bad
    · exact Or.inl ⟨by
        have member:=good.1
        simp only [List.mem_cons] at member
        rcases member with equal|equal|member
        · exact False.elim (notChild (GeneralBorrowNodeUpdate.index_injective _ _ equal))
        · exact False.elim (notExpr (GeneralBorrowNodeUpdate.index_injective _ _ equal))
        · exact member,good.2⟩
    · exact Or.inr ⟨fun member=>bad.1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)),bad.2⟩
  let base:=GeneralBorrowExposedScopedInactiveLeafSeed.seed tree location protections target selected head tail support (fun _=>true) context
    data.base.base.forest component data.base.support_eq mixed rootPath ancestors data.base.base.separate
    data.base.base.coherent data.short (by
      intro query included
      obtain ⟨node,present,leaf,exposed⟩:=data.leaves query included
      have good:=data.writableLeaves query node included present
      exact ⟨node,present,leaf,exposed,GeneralBorrowSparseExposedLeafState.supports _ _ good .Read,good.1⟩) first rest
  exact ⟨⟨base,data.base.support_eq,mixed⟩,data.short,data.leaves,data.writableLeaves⟩
/-- Restore the complete borrowed window on the same physical post-copy tree. -/
theorem owned_on (tree : BorrowTree) (protections : ProtectedTags)
    (child expr target selected head : UniIndex) (tail : List UniIndex) (support : Nat→Prop)
    (lower upper : UInt64)
    (owned : GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty
      (GeneralBorrowExposedScopedInactiveWritableReadData.Data tree location protections child selected head tail support (fun _=>true))) lower upper tree.locations)
    (childContext : GeneralBorrowExposedKnownRootRangeData.Context tree child selected head tail)
    (targetNode exprNode childNode : TreeNode) (targetPresent : tree.nodeAt target=some targetNode)
    (exprPresent : tree.nodeAt expr=some exprNode) (childPresent : tree.nodeAt child=some childNode)
    (exprHidden : exprNode.isExposed=false) (childHidden : childNode.isExposed=false)
    (exprUnheld : protections.contains exprNode.tag=false) (childUnheld : protections.contains childNode.tag=false)
    (paths : ∀location : LocationTree,(source_normal_projection tree location protections).topology.ancestorPath child.toNat=
      child.toNat::expr.toNat::(source_normal_projection tree location protections).topology.ancestorPath target.toNat)
    (first : head≠selected→area.support head) (rest : ∀root∈tail,root≠selected→area.support root) :
    ∃ context : GeneralBorrowExposedKnownRootRangeData.Context tree target selected head tail,
      GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty
        (GeneralBorrowExposedScopedInactiveWritableReadData.Data tree location protections target selected head tail support (fun _=>true))) lower upper tree.locations := by
  refine ⟨{childContext with anchorNode:=targetNode,anchorPresent:=targetPresent},?_⟩
  intro position valid positive beforeUpper afterLower
  obtain ⟨data⟩:=owned position valid positive beforeUpper afterLower
  exact ⟨restore tree _ protections child expr target selected head tail support data childContext targetNode exprNode childNode
    targetPresent exprPresent childPresent exprHidden childHidden exprUnheld childUnheld paths first rest⟩

end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableTwoRestore
