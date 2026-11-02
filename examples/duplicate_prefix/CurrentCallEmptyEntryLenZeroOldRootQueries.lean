import duplicate_prefix.CurrentCallEmptyEntryLenZeroOldRootFrame
import duplicate_prefix.CurrentCallEmptyEntryRepairedMetadata
import duplicate_prefix.GeneralBorrowSifaWritableFrame

namespace DuplicatePrefix.CurrentCallEmptyEntryLenZeroOldRootQueries
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedNonleafPrimaryPath DuplicatePrefixResidualSupportAuthorization CandidateStableCallOwnership
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] UniValMap.insert

private theorem fields {tree : BorrowTree} {parentTag tag : BorTag}
    (input : EmptyForestSharedPool.Input tree parentTag tag) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) :
    ∃ next,input.after.nodes.get index = some next ∧ next.parent = node.parent ∧ next.tag = node.tag ∧
      next.isExposed = node.isExposed ∧ next.defaultInitialPermission = node.defaultInitialPermission := by
  let staged := S04ZeroReadSharedAttach.liftNode input.parent input.index index node
  have atStage : input.stage.nodeAt index = some staged := by
    exact S04ZeroReadSharedAttach.old_lookup tree input.index input.parent input.parentNode
      (GeneralBorrowFreshAnchor.sharedNode tag input.parent) input.vacant input.present index node present
  obtain ⟨next,found,tagEq,parentEq,_,permission,exposure⟩ := GeneralBorrowFreshMetadataChildSifa.node_fields
    input.stage input.parent .Read index staged atStage
  change input.after.nodes.get index = some next at found
  have stable : staged.parent = node.parent ∧ staged.tag = node.tag ∧ staged.isExposed = node.isExposed ∧
      staged.defaultInitialPermission = node.defaultInitialPermission := by
    by_cases same : index = input.parent <;>
      simp only [staged,S04ZeroReadSharedAttach.liftNode,same,ite_true,ite_false,and_self]
  exact ⟨next,found,parentEq.trans stable.1,tagEq.trans stable.2.1,
    exposure.trans stable.2.2.1,permission.trans stable.2.2.2⟩

private theorem exposed_back {tree : BorrowTree} {parentTag tag : BorTag}
    (input : EmptyForestSharedPool.Input tree parentTag tag) (index : UniIndex) (node : TreeNode)
    (present : input.after.nodes.get index = some node) (exposed : node.isExposed = true) :
    ∃ old,tree.nodes.get index = some old := by
  by_cases fresh : index = input.index
  · subst index
    obtain ⟨child,found,hidden⟩ := input.node_exists
    have same := Option.some.inj (found.symm.trans present)
    subst child
    rw [exposed] at hidden
    cases hidden
  · by_cases parent : index = input.parent
    · subst index
      exact ⟨input.parentNode,input.present⟩
    · obtain ⟨staged,found,_⟩ := GeneralBorrowFreshMetadata.node_exists input.after input.stage
        (GeneralBorrowSifaView.preserves input.stage input.parent .Read).symm index node present
      change ((tree.nodes.insert input.index (GeneralBorrowFreshAnchor.sharedNode tag input.parent)).insert
        input.parent (GeneralBorrowFreshGraph.updatedParent input.parentNode input.index)).get index = some staged at found
      rw [GeneralBorrowFreshLocation.get_other _ _ _ _ parent,
        GeneralBorrowFreshLocation.get_other _ _ _ _ fresh] at found
      exact ⟨staged,found⟩

/-- The two actual zero Shared helpers retain each disjoint original root's
repaired authorization and current source-relative masked query geometry. -/
theorem queries {tree : BorrowTree} {parentTag tag1 tag2 : BorTag}
    (first : EmptyForestSharedPool.Input tree parentTag tag1)
    (second : EmptyForestSharedPool.Input first.after tag1 tag2)
    (secondParent : second.parent = first.index) (parentless : first.parentNode.parent = none)
    (current : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop)
    (different : root ≠ first.parent)
    (supported : ∀ query,support query → Path tree root query)
    (old : DuplicatePrefixResidualWriteRepaired.Authorization tree current protections root position maximum kind support)
    (beforeC afterC : Completion) (source : UniIndex)
    (classification : ∀ removed,Removal tree current protections maximum kind removed →
      ∀ query node,support query → tree.nodes.get query = some node →
      let relation := residualRelation tree current protections root query node maximum kind position removed
      (Below beforeC query source → relation = some .LocalAccess ∨ relation = some .EitherAccess) ∧
      (¬Below beforeC query source → relation = some .ForeignAccess ∨ relation = some .EitherAccess))
    (ancestry : ∀ query,support query → (Below afterC query source ↔ Below beforeC query source)) :
    DuplicatePrefixResidualWriteRepaired.Authorization second.after current protections root position maximum kind support ∧
      ∀ removed,Removal second.after current protections maximum kind removed →
      ∀ query node,support query → second.after.nodes.get query = some node →
      let relation := residualRelation second.after current protections root query node maximum kind position removed
      (Below afterC query source → relation = some .LocalAccess ∨ relation = some .EitherAccess) ∧
      (¬Below afterC query source → relation = some .ForeignAccess ∨ relation = some .EitherAccess) := by
  have size1 := EmptyForestSharedPoolNext.node_size first
  have size2 := EmptyForestSharedPoolNext.node_size second
  apply CurrentCallEmptyEntryRepairedMetadata.queries tree second.after current current protections
    first.depth second.afterDepth (by omega) _ _ root position maximum kind support old
    (fun query included => CurrentCallEmptyEntryLenZeroOldRootFrame.nodes first second secondParent parentless
      root query different (supported query included)) (fun _ _ => rfl) beforeC afterC source classification ancestry
  · intro index node present
    obtain ⟨middle,middleAt,parent1,tag1,exposure1,permission1⟩ := fields first index node present
    obtain ⟨next,nextAt,parent2,tag2,exposure2,permission2⟩ := fields second index middle middleAt
    refine ⟨next,nextAt,parent2.trans parent1,tag2.trans tag1,exposure2.trans exposure1,?_⟩
    exact congrArg Prod.fst (GeneralBorrowSifaWritableFrame.effective_shape current current index node next rfl
      (permission2.trans permission1))
  · intro index next present exposed
    obtain ⟨middle,middleAt⟩ := exposed_back second index next present exposed
    obtain ⟨actual,found,_,_,exposure,_⟩ := fields second index middle middleAt
    have same := Option.some.inj (found.symm.trans present)
    subst actual
    exact exposed_back first index middle middleAt (exposure.symm.trans exposed)

end DuplicatePrefix.CurrentCallEmptyEntryLenZeroOldRootQueries

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryLenZeroOldRootQueries" then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved old-root query dependency {dependency}"
