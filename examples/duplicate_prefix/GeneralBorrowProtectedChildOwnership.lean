import duplicate_prefix.GeneralBorrowRootChildWriteOwnership
import duplicate_prefix.GeneralBorrowFreshReuseProtection
import duplicate_prefix.GeneralBorrowProtectedMutableRelease

namespace DuplicatePrefix.GeneralBorrowProtectedChildOwnership
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.BorrowRangeAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The real singleton registration protects only the actual new child's slot;
node-to-tag accounting excludes a second node with the same tag. -/
theorem held_only (tree : BorrowTree) (location : LocationTree) (tag : BorTag) (child : UniIndex)
    (lookup : tree.indexOfTag tag = some child)
    (nodeTags : ∀ index node, tree.nodeAt index = some node → tree.indexOfTag node.tag = some index)
    (position : Nat)
    (held : (source_normal_projection tree location (({} : ProtectedTags).insert tag .StrongProtector)).protectedNodes.contains position = true) :
    position = child.toNat := by
  revert held
  unfold_general_projection
  intro held
  simp only [List.contains_iff_mem,List.mem_filterMap] at held
  obtain ⟨⟨index,node⟩,member,selected⟩ := held
  have chosen : index.toNat = position ∧ (({} : ProtectedTags).insert tag .StrongProtector).contains node.tag = true := by
    split at selected
    next active => exact ⟨Option.some.inj selected,active⟩
    next => contradiction
  have tagged : node.tag = tag := by
    exact (show tag = node.tag by simpa [ProtectedTags.contains,ProtectedTags.get,ProtectedTags.insert] using chosen.2).symm
  have present := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mp member
  have mapped := nodeTags index node present
  rw [tagged,lookup] at mapped
  exact chosen.1.symm.trans (congrArg UniIndex.toNat (Option.some.inj mapped).symm)

/-- Counterfactual unheld root ownership and a real reserved child imply actual
child Write ownership under the singleton registration, on every interval. This
does not assert actual registered ROOT Write ownership. -/
theorem child (tree : BorrowTree) (location : LocationTree) (root child : UniIndex) (rootNode childNode : TreeNode)
    (rootPresent : tree.nodeAt root = some rootNode) (rootless : rootNode.parent = none)
    (childPresent : tree.nodeAt child = some childNode) (parent : childNode.parent = some root)
    (tag : BorTag) (lookup : tree.indexOfTag tag = some child)
    (nodeTags : ∀ index node, tree.nodeAt index = some node → tree.indexOfTag node.tag = some index)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location {}) root.toNat .Write)
    (reserved : ∀ state, (source_normal_projection tree location {}).stateAt child.toNat = some state → state.permission = .ReservedFrz false) :
    GeneralBorrowAnchor.AnchorOwned
      (source_normal_projection tree location (({} : ProtectedTags).insert tag .StrongProtector)) child.toNat .Write := by
  have base := GeneralBorrowRootChildWriteOwnership.child_of_root tree location root child rootNode childNode
    rootPresent rootless childPresent parent owned reserved
  have path := GeneralBorrowRootChildWriteOwnership.paths tree location root child rootNode childNode rootPresent rootless childPresent parent
  rw [GeneralBorrowFreshProtectorRelease.projection_protections tree location {} (({} : ProtectedTags).insert tag .StrongProtector)]
  refine ⟨base.anchorValid,base.locationsAligned,base.defaultsAligned,?_⟩
  intro position valid
  obtain ⟨state,present,permission⟩ := base.permissions position valid
  refine ⟨state,present,?_⟩
  by_cases same : position = child.toNat
  · subst position
    have exactPerm := reserved state present
    change GeneralBorrowPermissions.AccessOwned state .Write
      (GeneralBorrowAnchor.relation (source_normal_projection tree location {}) child.toNat child.toNat) _
    rw [GeneralBorrowAnchor.relation,path.2]
    simp only [List.mem_cons,true_or,ite_true]
    change GeneralBorrowPermissions.LocalOwned state _
    rcases state with ⟨p,a,s⟩
    cases exactPerm
    cases a <;> cases s <;> exact ⟨rfl,True.intro⟩
  · have notHeld : (source_normal_projection tree location (({} : ProtectedTags).insert tag .StrongProtector)).protectedNodes.contains position = false := by
      cases active : (source_normal_projection tree location (({} : ProtectedTags).insert tag .StrongProtector)).protectedNodes.contains position with
      | false => rfl
      | true => exact False.elim (same (held_only tree location tag child lookup nodeTags position active))
    have empty : (source_normal_projection tree location {}).protectedNodes.contains position = false := by
      unfold_general_projection
      simp [ProtectedTags.contains,ProtectedTags.get]
    simpa only [GeneralBorrowAnchor.relation,notHeld,empty] using permission

end DuplicatePrefix.GeneralBorrowProtectedChildOwnership
