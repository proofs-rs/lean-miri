import duplicate_prefix.GeneralBorrowExposedScopedRestore
import duplicate_prefix.GeneralBorrowExposedKnownRootRangeData
import duplicate_prefix.GeneralBorrowFreshRestoreData
import duplicate_prefix.GeneralBorrowFreshSharedPaths
namespace DuplicatePrefix.GeneralBorrowExposedScopedWriteRestore
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
    (child target selected head : UniIndex) (tail : List UniIndex)
    (data : GeneralBorrowExposedKnownRootRangeData.Data tree location protections child selected head tail .Write)
    (targetNode childNode : TreeNode) (targetPresent : tree.nodeAt target=some targetNode)
    (childPresent : tree.nodeAt child=some childNode)
    (childUnheld : protections.contains childNode.tag=false)
    (paths : ∀ location : LocationTree,(source_normal_projection tree location protections).topology.ancestorPath child.toNat=
      child.toNat::(source_normal_projection tree location protections).topology.ancestorPath target.toNat) :
    GeneralBorrowExposedKnownRootRangeData.Data tree location protections target selected head tail .Write := by
  have subset (row : LocationTree) (position : Nat)
      (member : position∈(source_normal_projection tree row protections).topology.ancestorPath target.toNat) :
      position∈(source_normal_projection tree row protections).topology.ancestorPath child.toNat := by
    rw [paths row]
    exact List.mem_cons_of_mem _ member
  have restoration := GeneralBorrowFreshRestoreData.from_paths tree protections protections child target targetNode targetPresent subset (by
    intro row index node present localChild foreignTarget
    rw [paths row] at localChild
    rcases List.mem_cons.mp localChild with equal | member
    · have same : index=child := GeneralBorrowNodeUpdate.index_injective index child equal
      subst index
      have nodeEq : node=childNode := Option.some.inj (present.symm.trans childPresent)
      subst node
      exact childUnheld
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
    simpa only [List.getLast!_eq_getLast?_getD,List.getLast?_cons_of_ne_nil nonempty] using previous
  let component : GeneralBorrowExposedScopedNormal.Component (source_normal_projection tree location protections).topology target.toNat := {
    support := data.component.support
    anchor := supported
    parents := data.component.parents
    children := data.component.children }
  refine ⟨data.forest,component,?_,targetPath,data.hidden,data.separate,data.coherent,data.profile,data.primary,data.virtual⟩
  intro index inside valid
  have size : (source_normal_projection tree location protections).locationStates.size = (source_normal_projection tree location protections).topology.nodes.size := by
    unfold_general_projection
    unfold_general_topology
    simp only [Array.size_map,Array.size_mapIdx]
  exact recovered index inside (by rw [size];exact valid)

/-- Range-wide direct-child restoration after physical copy retains all raw
callbacks needed by the original ROOT's implicit Write release. -/
theorem owned_on (tree : BorrowTree) (protections : ProtectedTags)
    (child target selected head : UniIndex) (tail : List UniIndex)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree child selected head tail)
    (targetNode childNode : TreeNode) (targetPresent : tree.nodeAt target=some targetNode)
    (childPresent : tree.nodeAt child=some childNode) (childUnheld : protections.contains childNode.tag=false)
    (paths : ∀ location : LocationTree,(source_normal_projection tree location protections).topology.ancestorPath child.toNat=
      child.toNat::(source_normal_projection tree location protections).topology.ancestorPath target.toNat)
    (lower upper : UInt64)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (fun location=>Nonempty (GeneralBorrowExposedKnownRootRangeData.Data tree location protections child selected head tail .Write)) lower upper tree.locations) :
    Nonempty (GeneralBorrowExposedKnownRootRangeData.Context tree target selected head tail) ∧
    GeneralRangeMapOrigins.OwnedOn
      (fun location=>Nonempty (GeneralBorrowExposedKnownRootRangeData.Data tree location protections target selected head tail .Write)) lower upper tree.locations := by
  refine ⟨⟨{context with anchorNode:=targetNode,anchorPresent:=targetPresent}⟩,?_⟩
  intro position valid positive beforeUpper afterLower
  obtain ⟨data⟩ := owned position valid positive beforeUpper afterLower
  exact ⟨restore tree _ protections child target selected head tail data targetNode childNode targetPresent childPresent childUnheld paths⟩
end DuplicatePrefix.GeneralBorrowExposedScopedWriteRestore
