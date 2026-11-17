import duplicate_prefix.GeneralBorrowSharedAuthorizationExtension

namespace DuplicatePrefix.GeneralBorrowSharedAuthorizationRemoval
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowFreshNode GeneralBorrowNodeUpdate
open DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 200000
attribute [local irreducible] UniValMap.insert

/-- Hidden child insertion cannot create a removable contribution, and changing
only child arrays preserves the removal policy on every existing node. -/
theorem attached_removal (tree : BorrowTree)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodes.get parent = some parentNode)
    (hidden : newNode.isExposed = false)
    (before after : LocationTree) (protections : ProtectedTags)
    (slots : ∀ query node, tree.nodes.get query = some node → after.perms.get query = before.perms.get query)
    (maximum : Option BorTag) (kind : AccessKind) (removed : List UniIndex)
    (legal : Removal {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode}
      after protections maximum kind removed) :
    Removal tree before protections maximum kind removed := by
  have different : parent ≠ index := by
    intro same;rw [same,vacant] at parentPresent;cases parentPresent
  have parentAfter : (tree.nodes.insert index newNode).get parent = some parentNode :=
    (GeneralBorrowFreshLocation.get_other tree.nodes index parent newNode different).trans parentPresent
  refine ⟨legal.distinct,?_⟩
  intro query member
  obtain ⟨node,present,allowed⟩ := legal.allowed query member
  by_cases isIndex : query = index
  · subst query
    have found : (attachedNodes tree.nodes index parent parentNode newNode).get index = some newNode := by
      unfold attachedNodes
      rw [GeneralBorrowFreshLocation.get_other _ parent index _ (Ne.symm different),GeneralBorrowFreshLocation.get_same]
    have equal := Option.some.inj (found.symm.trans present)
    subst node
    cases kind <;> simp [removable,hidden] at allowed
  · by_cases isParent : query = parent
    · subst query
      have found : (attachedNodes tree.nodes index parent parentNode newNode).get parent =
          some {parentNode with children := parentNode.children.push index} :=
        insert_existing_get_same (tree.nodes.insert index newNode) parent parentNode _ parentAfter
      have equal := Option.some.inj (found.symm.trans present)
      subst node
      refine ⟨parentNode,parentPresent,?_⟩
      change removable before protections maximum kind parent parentNode = true
      change removable after protections maximum kind parent parentNode = true at allowed
      simpa only [removable,effective,slots parent parentNode parentPresent] using allowed
    · have oldPresent : tree.nodes.get query = some node := by
        change ((tree.nodes.insert index newNode).insert parent _).get query = some node at present
        rw [GeneralBorrowFreshLocation.get_other _ parent query _ isParent,
          GeneralBorrowFreshLocation.get_other _ index query _ isIndex] at present
        exact present
      refine ⟨node,oldPresent,?_⟩
      simpa only [removable,effective,slots query node oldPresent] using allowed

end DuplicatePrefix.GeneralBorrowSharedAuthorizationRemoval
