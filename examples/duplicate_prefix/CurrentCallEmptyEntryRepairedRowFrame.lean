import duplicate_prefix.GeneralBorrowRootLocalAuthorization
import duplicate_prefix.DuplicatePrefixResidualWriteRepaired
import duplicate_prefix.CandidateStableCallOwnership

namespace DuplicatePrefix.CurrentCallEmptyEntryRepairedRowFrame
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposureAncestorFold GeneralBorrowExposedNonleafPrimaryPath
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
open GeneralBorrowRootLocalAuthorization CandidateStableCallOwnership
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Full any-kind/any-cutoff residual authorization transports across an
unchanged root component. Current legal masks are filtered internally; they
need not be empty, and permissions outside the component may change freely.
This data theorem needs no coherent-cache or finite-width assumption. -/
private theorem authorization_walk (tree : BorrowTree) (before after : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop)
    (old : DuplicatePrefixResidualWriteRepaired.Authorization tree before protections root position maximum kind support)
    (slots : ∀ index node, tree.nodes.get index = some node →
      root ∈ walk tree.nodes (tree.nodes.size+1) index → after.perms.get index = before.perms.get index) :
    DuplicatePrefixResidualWriteRepaired.Authorization tree after protections root position maximum kind support := by
  have supportSlots : ∀ index, support index → after.perms.get index = before.perms.get index := by
    intro index inside
    obtain ⟨node,present⟩ := old.present index inside
    apply slots index node present
    apply old.covers index inside (index,node) ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present)
    simp [walk]
  refine ⟨old.rooted,old.present,old.children,old.covers,?_,?_,?_⟩
  · intro index node inside present
    simpa only [supportSlots index inside] using old.possible index node inside present
  · intro entry exit legalEntry legalExit subset index node inside present retained
    have oldEntry := mask_legal tree before after protections root maximum kind entry legalEntry slots
    have oldExit := mask_legal tree before after protections root maximum kind exit legalExit slots
    have nested := mask_subset tree root entry exit subset
    have notRemoved : index ∉ componentMask tree root exit := by
      intro member
      exact retained ((componentMask_member tree root exit index).mp member).1
    rw [relation_frame tree before after protections root index node position maximum kind entry (old.covers index inside) slots,
      relation_frame tree before after protections root index node position maximum kind exit (old.covers index inside) slots]
    simpa only [supportSlots index inside] using old.queries _ _ oldEntry oldExit nested index node inside present notRemoved
  · intro physical
    obtain ⟨index,node,inside,present,witness⟩ := old.witness physical
    exact ⟨index,node,inside,present,by simpa only [Supports,supportSlots index inside] using witness⟩

/-- A repaired callback survives a frame of its physical component. Legal
masks are restricted internally to that component; unrelated roots are free
to change permissions and mask eligibility. -/
theorem authorization (tree : BorrowTree) (before after : LocationTree) (protections : ProtectedTags)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop)
    (old : DuplicatePrefixResidualWriteRepaired.Authorization tree before protections root position maximum kind support)
    (slots : ∀ index node,tree.nodes.get index = some node → Path tree root index →
      after.perms.get index = before.perms.get index) :
    DuplicatePrefixResidualWriteRepaired.Authorization tree after protections root position maximum kind support := by
  apply authorization_walk tree before after protections root position maximum kind support old
  intro index node present walk
  exact slots index node present (GeneralBorrowWildcardControlWitness.path_of_walk tree depth root index node present _ walk)

/-- The SAME source-relative classification follows the actual component's
row frame together with repaired authorization. Only internally filtered legal
masks are used at the original factory row. -/
theorem queries (tree : BorrowTree) (before after : LocationTree) (protections : ProtectedTags)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop)
    (old : DuplicatePrefixResidualWriteRepaired.Authorization tree before protections root position maximum kind support)
    (slots : ∀ index node,tree.nodes.get index = some node → Path tree root index →
      after.perms.get index = before.perms.get index)
    (completion : Completion) (source : UniIndex)
    (classification : ∀ removed,Removal tree before protections maximum kind removed →
      ∀ query node,support query → tree.nodes.get query = some node →
      let relation := residualRelation tree before protections root query node maximum kind position removed
      (Below completion query source → relation = some .LocalAccess ∨ relation = some .EitherAccess) ∧
      (¬Below completion query source → relation = some .ForeignAccess ∨ relation = some .EitherAccess)) :
    DuplicatePrefixResidualWriteRepaired.Authorization tree after protections root position maximum kind support ∧
      ∀ removed,Removal tree after protections maximum kind removed →
      ∀ query node,support query → tree.nodes.get query = some node →
      let relation := residualRelation tree after protections root query node maximum kind position removed
      (Below completion query source → relation = some .LocalAccess ∨ relation = some .EitherAccess) ∧
      (¬Below completion query source → relation = some .ForeignAccess ∨ relation = some .EitherAccess) := by
  have componentSlots : ∀ index node,tree.nodes.get index = some node →
      root ∈ walk tree.nodes (tree.nodes.size+1) index → after.perms.get index = before.perms.get index := by
    intro index node present member
    exact slots index node present (GeneralBorrowWildcardControlWitness.path_of_walk tree depth root index node present _ member)
  refine ⟨authorization tree before after protections depth root position maximum kind support old slots,?_⟩
  intro removed legal query node included present
  have oldLegal := mask_legal tree before after protections root maximum kind removed legal componentSlots
  have equal := relation_frame tree before after protections root query node position maximum kind removed
    (old.covers query included) componentSlots
  dsimp only
  rw [equal]
  exact classification _ oldLegal query node included present

end DuplicatePrefix.CurrentCallEmptyEntryRepairedRowFrame

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryRepairedRowFrame" then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved repaired row frame dependency {dependency}"
