import duplicate_prefix.GeneralBorrowExposedScopedRestore
import duplicate_prefix.GeneralBorrowExposedKnownRootRangeData
import duplicate_prefix.GeneralBorrowFreshRestoreData
import duplicate_prefix.GeneralBorrowFreshSharedPaths
import duplicate_prefix.GeneralBorrowExposedScopedLeafWriteReadClosed
import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationBounds
namespace DuplicatePrefix.GeneralBorrowExposedScopedTwoWriteReadRestore
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- After an actual mutable helper has ended, a direct unprotected child can
return its full Write invariant to the older target. Only raw graph paths and
child-tag absence are required; restored ownership is derived. -/
noncomputable def restore (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (child expr target selected head : UniIndex) (tail : List UniIndex)
    (strong : GeneralBorrowExposedScopedLeafWriteReadClosed.Data tree location protections child selected head tail)
    (targetNode exprNode childNode : TreeNode) (targetPresent : tree.nodeAt target=some targetNode)
    (exprPresent : tree.nodeAt expr=some exprNode) (exprUnheld : protections.contains exprNode.tag=false)
    (childPresent : tree.nodeAt child=some childNode)
    (childUnheld : protections.contains childNode.tag=false)
    (paths : ∀ location : LocationTree,(source_normal_projection tree location protections).topology.ancestorPath child.toNat=
      child.toNat::expr.toNat::(source_normal_projection tree location protections).topology.ancestorPath target.toNat) :
    GeneralBorrowExposedScopedLeafWriteReadClosed.Data tree location protections target selected head tail := by
  let data:=strong.write
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
  have supported : data.component.support target.toNat :=
    GeneralBorrowPresence.ancestors_present _ data.component.support data.component.parents _ child.toNat data.component.anchor _
      (subset location target.toNat (GeneralBorrowFreshSharedPaths.ancestor_self _ target.toNat))
  have mixed : GeneralBorrowExposedScopedOwnership.Pointwise data.component.support
      (source_normal_projection tree location protections) (fun _=>true)
      (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) child.toNat) := by
    intro index inside valid
    have size : (source_normal_projection tree location protections).locationStates.size = (source_normal_projection tree location protections).topology.nodes.size := by
      unfold_general_projection
      unfold_general_topology
      simp only [Array.size_map,Array.size_mapIdx]
    exact data.owned index inside (by rw [←size];exact valid)
  have recovered := GeneralBorrowExposedScopedRestore.location tree location protections protections (fun _ held=>held)
    child target data.component.support (fun _=>true) restoration mixed
  have targetPath : ((source_normal_projection tree location protections).topology.ancestorPath target.toNat).getLast!=selected.toNat := by
    have self:=GeneralBorrowFreshSharedPaths.ancestor_self (source_normal_projection tree location protections).topology target.toNat
    have nonempty : (source_normal_projection tree location protections).topology.ancestorPath target.toNat≠[] := by
      intro empty;rw [empty] at self;cases self
    have previous:=data.rootPath
    rw [paths location] at previous
    have extended : expr.toNat::(source_normal_projection tree location protections).topology.ancestorPath target.toNat≠[] := by simp
    simpa only [List.getLast!_eq_getLast?_getD,List.getLast?_cons_of_ne_nil extended,List.getLast?_cons_of_ne_nil nonempty] using previous
  let component : GeneralBorrowExposedScopedNormal.Component (source_normal_projection tree location protections).topology target.toNat := {
    support := data.component.support
    anchor := supported
    parents := data.component.parents
    children := data.component.children }
  refine ⟨⟨data.forest,component,?_,targetPath,data.hidden,data.separate,data.coherent,data.profile,data.primary,data.virtual⟩,strong.short,strong.leaves,strong.positive⟩
  intro index inside valid
  have size : (source_normal_projection tree location protections).locationStates.size = (source_normal_projection tree location protections).topology.nodes.size := by
    unfold_general_projection
    unfold_general_topology
    simp only [Array.size_map,Array.size_mapIdx]
  exact recovered index inside (by rw [size];exact valid)


omit area in
/-- Both escaping tags are discharged from the actual singleton helper frame.
The expression tag was initially absent; the helper tag is really registered. -/
theorem ended_unheld (global : GlobalState) (id : AllocId) (expr child : BorTag)
    (exprFree : global.protectedTags.contains expr=false) :
    let ended:=global.endCall (({} : FrameState).addProtector id child)
    ended.protectedTags.contains expr=false ∧ ended.protectedTags.contains child=false := by
  constructor
  · have preserved:=GeneralBorrowRelease.remove_fold_absent ((({} : FrameState).addProtector id child).protectedTags.toList) global.protectedTags expr exprFree
    simpa only [GlobalState.endCall,Array.foldl_toList] using preserved
  · exact GeneralBorrowRelease.end_call_owned_absent global _ id child (by simp [FrameState.addProtector])

omit area in
/-- Source counter freshness, rather than a post-copy table guard, establishes
that an expression-issued tag cannot be an earlier registered protector. -/
theorem issued_unheld (global : GlobalState) (bound : Nat)
    (below : GeneralBorrowProtectedSiblingGenerationBounds.ProtectedBelow global.protectedTags bound)
    (expr : BorTag) (issued : bound≤expr.value.toNat) : global.protectedTags.contains expr=false := by
  unfold ProtectedTags.contains
  rw [GeneralBorrowProtectedSiblingGenerationBounds.unheld global.protectedTags bound below expr issued]
  rfl

/-- Two real mutable layers restore both original-target callbacks after copy.
Only actual graph paths and absent escaping tags supplement the strong data
returned by the real copy; no ownership or operation success is assumed. -/
theorem owned_on (tree : BorrowTree) (protections : ProtectedTags)
    (child expr target selected head : UniIndex) (tail : List UniIndex)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree child selected head tail)
    (targetNode exprNode childNode : TreeNode) (targetPresent : tree.nodeAt target=some targetNode)
    (exprPresent : tree.nodeAt expr=some exprNode) (exprUnheld : protections.contains exprNode.tag=false)
    (childPresent : tree.nodeAt child=some childNode) (childUnheld : protections.contains childNode.tag=false)
    (paths : ∀ location : LocationTree,(source_normal_projection tree location protections).topology.ancestorPath child.toNat=
      child.toNat::expr.toNat::(source_normal_projection tree location protections).topology.ancestorPath target.toNat)
    (lower upper : UInt64)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (fun location=>Nonempty (GeneralBorrowExposedScopedLeafWriteReadClosed.Data tree location protections child selected head tail)) lower upper tree.locations) :
    Nonempty (GeneralBorrowExposedKnownRootRangeData.Context tree target selected head tail) ∧
    (∀ kind,GeneralRangeMapOrigins.OwnedOn
      (fun location=>Nonempty (GeneralBorrowExposedKnownRootRangeData.Data tree location protections target selected head tail kind)) lower upper tree.locations) := by
  let targetContext : GeneralBorrowExposedKnownRootRangeData.Context tree target selected head tail:=
    {context with anchorNode:=targetNode,anchorPresent:=targetPresent}
  refine ⟨⟨targetContext⟩,?_⟩
  intro kind position valid positive beforeUpper afterLower
  obtain ⟨data⟩:=owned position valid positive beforeUpper afterLower
  let next:=restore tree _ protections child expr target selected head tail data targetNode exprNode childNode
    targetPresent exprPresent exprUnheld childPresent childUnheld paths
  cases kind with
  | Read => exact ⟨GeneralBorrowExposedScopedLeafWriteReadClosed.read tree _ protections target selected head tail targetContext next⟩
  | Write => exact ⟨next.write⟩
end DuplicatePrefix.GeneralBorrowExposedScopedTwoWriteReadRestore
