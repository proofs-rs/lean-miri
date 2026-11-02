import duplicate_prefix.GeneralBorrowExposureChildAttach
import duplicate_prefix.GeneralBorrowRootLocalAuthorization

namespace DuplicatePrefix.GeneralBorrowSharedAuthorizationExtension
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposureAncestorFold GeneralBorrowExposureGraphTransport
open DuplicatePrefixResidualSupportAuthorization GeneralBorrowFreshNode GeneralBorrowNodeUpdate
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 200000
attribute [local irreducible] UniValMap.insert

/-- Contribution indices, with arbitrary finite removals, depend only on old
parent links and exposed levels. Fresh hidden nodes contribute nothing, even
when their reusable slot previously had arbitrary permission storage. -/
theorem masked_count_extension (before after : BorrowTree)
    (oldLocation newLocation : LocationTree) (protections : ProtectedTags)
    (depth : GeneralBorrowExposure.ParentDepth before.nodes)
    (size : before.nodes.size ≤ after.nodes.size)
    (old : ∀ index node, before.nodes.get index = some node →
      ∃ next, after.nodes.get index = some next ∧ next.parent = node.parent ∧
        next.isExposed = node.isExposed ∧
        effective newLocation protections index next = effective oldLocation protections index node)
    (back : ∀ index next, after.nodes.get index = some next → next.isExposed = true →
      ∃ node, before.nodes.get index = some node)
    (removed : List UniIndex) (query : UniIndex) (kind : AccessKind) :
    residualCount after newLocation protections kind removed query =
      residualCount before oldLocation protections kind removed query := by
  have masked (tree : BorrowTree) (location : LocationTree) :
      residualCount tree location protections kind removed query =
      cardinality tree.nodes
        (fun index node => if removed.contains index then .None else effective location protections index node)
        query kind := by
    unfold residualCount cardinality
    rw [List.filter_filter]
    apply congrArg List.length
    apply List.filter_congr
    intro row member
    by_cases mem : removed.contains row.1 = true
    · cases kind <;> simp only [contributes,mem,ite_true,supports,supportsRead,supportsWrite,Bool.not_true,Bool.and_false,Bool.false_and]
    · have absent : removed.contains row.1 = false := Bool.eq_false_iff.mpr mem
      simp only [contributes,absent,Bool.false_eq_true,ite_false,Bool.not_false,Bool.true_and]
  rw [masked,masked]
  apply extension before.nodes after.nodes depth _ _ size _ back query kind
  intro index node present
  obtain ⟨next,found,parent,exposed,level⟩ := old index node present
  refine ⟨next,found,parent,exposed,?_⟩
  simp only [level]

/-- Instantiates the data extension at the exact two node insertions used by
shared newChild; index vacancy permits both append and bounded reuse. -/
theorem attached_masked_count (tree : BorrowTree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodes.get parent = some parentNode)
    (hidden : newNode.isExposed = false)
    (size : tree.nodes.size ≤ (attachedNodes tree.nodes index parent parentNode newNode).size)
    (before after : LocationTree) (protections : ProtectedTags)
    (slots : ∀ query node,tree.nodes.get query = some node → after.perms.get query = before.perms.get query)
    (removed : List UniIndex) (query : UniIndex) (kind : AccessKind) :
    residualCount {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode}
      after protections kind removed query = residualCount tree before protections kind removed query := by
  have parentDifferent : parent ≠ index := by
    intro same; rw [same,vacant] at parentPresent; cases parentPresent
  have parentAfter : (tree.nodes.insert index newNode).get parent = some parentNode :=
    (GeneralBorrowFreshLocation.get_other tree.nodes index parent newNode parentDifferent).trans parentPresent
  apply masked_count_extension tree _ before after protections depth size
  · intro old oldNode present
    have different : old ≠ index := by intro same;rw [same,vacant] at present;cases present
    by_cases isParent : old = parent
    · subst old
      have equal : oldNode = parentNode := Option.some.inj (present.symm.trans parentPresent)
      subst oldNode
      refine ⟨{parentNode with children := parentNode.children.push index},
        insert_existing_get_same (tree.nodes.insert index newNode) parent parentNode _ parentAfter,rfl,rfl,?_⟩
      simp only [effective,slots parent parentNode parentPresent]
      rfl
    · refine ⟨oldNode,?_,rfl,rfl,?_⟩
      · change ((tree.nodes.insert index newNode).insert parent _).get old = _
        rw [GeneralBorrowFreshLocation.get_other _ parent old _ isParent,
          GeneralBorrowFreshLocation.get_other _ index old _ different,present]
      · simp only [effective,slots old oldNode present]
  · intro old oldNode present exposed
    by_cases isIndex : old = index
    · subst old
      have newPresent : (attachedNodes tree.nodes index parent parentNode newNode).get index = some newNode := by
        unfold attachedNodes
        rw [GeneralBorrowFreshLocation.get_other _ parent index _ (Ne.symm parentDifferent),GeneralBorrowFreshLocation.get_same]
      have equal := Option.some.inj (newPresent.symm.trans present)
      subst oldNode;rw [hidden] at exposed;cases exposed
    · by_cases isParent : old = parent
      · subst old;exact ⟨parentNode,parentPresent⟩
      · refine ⟨oldNode,?_⟩
        change ((tree.nodes.insert index newNode).insert parent _).get old = some oldNode at present
        rw [GeneralBorrowFreshLocation.get_other _ parent old _ isParent,
          GeneralBorrowFreshLocation.get_other _ index old _ isIndex] at present
        exact present

end DuplicatePrefix.GeneralBorrowSharedAuthorizationExtension
