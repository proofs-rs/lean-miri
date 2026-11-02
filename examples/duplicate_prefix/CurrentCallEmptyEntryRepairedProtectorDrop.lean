import duplicate_prefix.GeneralBorrowHiddenProtectorRowWeakens
import duplicate_prefix.DuplicatePrefixResidualWriteRepaired

namespace DuplicatePrefix.CurrentCallEmptyEntryRepairedProtectorDrop
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
open GeneralBorrowExposureCardinality
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem count_eq (tree : BorrowTree) (location : LocationTree) (before after : ProtectedTags)
    (same : ∀ index node, tree.nodeAt index = some node → node.isExposed = true → after.contains node.tag = before.contains node.tag)
    (kind : AccessKind) (removed : List UniIndex) (query : UniIndex) :
    residualCount tree location after kind removed query = residualCount tree location before kind removed query := by
  unfold residualCount
  congr 2
  apply List.filter_congr
  intro row member
  have present := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp member
  cases exposed : row.2.isExposed with
  | false => simp only [contributes,exposed,Bool.false_and]
  | true => simp only [contributes,effective,same row.1 row.2 present exposed]

private theorem removal (tree : BorrowTree) (location : LocationTree) (before after : ProtectedTags)
    (same : ∀ index node, tree.nodeAt index = some node → node.isExposed = true → after.contains node.tag = before.contains node.tag)
    (maximum : Option BorTag) (kind : AccessKind) (removed : List UniIndex)
    (legal : Removal tree location after maximum kind removed) : Removal tree location before maximum kind removed := by
  refine ⟨legal.distinct,?_⟩
  intro index member
  obtain ⟨node,present,allowed⟩ := legal.allowed index member
  refine ⟨node,present,?_⟩
  cases exposed : node.isExposed with
  | false => cases kind <;> simp [removable,exposed] at allowed
  | true => cases kind <;> simpa only [removable,effective,same index node present exposed] using allowed

private theorem scalar_old (state : LocationState) (kind : AccessKind) (before after : Bool)
    (weaken : after = true → before = true) (entry exit : Option WildcardAccessRelatedness)
    (old : DuplicatePrefixCallbackVisitAuthorization.Authorized state kind before entry exit) :
    DuplicatePrefixCallbackVisitAuthorization.Authorized state kind after entry exit := by
  refine ⟨old.1,?_⟩
  rcases old.2 with skipped | branch
  · exact .inl skipped
  · apply Or.inr
    cases exit with
    | none => exact branch
    | some related =>
      cases related with
      | EitherAccess => exact branch
      | LocalAccess | ForeignAccess => exact ⟨branch.1,GeneralBorrowParentRestoreScalar.weakens state kind _ before after weaken branch.2⟩

private theorem authorized (state : LocationState) (kind : AccessKind) (before after : Bool)
    (weaken : after = true → before = true) (entry exit : Option WildcardAccessRelatedness)
    (old : DuplicatePrefixCallbackVisitAuthorizationRepaired.Authorized state kind before entry exit) :
    DuplicatePrefixCallbackVisitAuthorizationRepaired.Authorized state kind after entry exit := by
  rcases old with legacy | repaired
  · exact .inl (scalar_old state kind before after weaken entry exit legacy)
  · have data := (DuplicatePrefixCallbackVisitAuthorizationRepaired.postchildren_noop_iff_data state kind before exit).mp repaired.2
    have unheld : before = false → after = false := by
      intro falseBefore
      cases actual : after with
      | false => rfl
      | true => have impossible := weaken actual; rw [falseBefore] at impossible; cases impossible
    refine .inr ⟨repaired.1,
      (DuplicatePrefixCallbackVisitAuthorizationRepaired.postchildren_noop_iff_data state kind after exit).mpr
        ⟨data.1,?_,data.2.2⟩⟩
    rcases data.2.1 with cell | ⟨disabled,quiet⟩ | ⟨reserved,free⟩
    · exact .inl cell
    · exact .inr (.inl ⟨disabled,quiet.imp unheld id⟩)
    · exact .inr (.inr ⟨reserved,unheld free⟩)

/-- Legal masks and actual classifications are unchanged when only hidden
protector membership drops. -/
theorem mask_frame (tree : BorrowTree) (location : LocationTree) (before after : ProtectedTags)
    (same : ∀ index node,tree.nodeAt index = some node → node.isExposed = true →
      after.contains node.tag = before.contains node.tag)
    (root query : UniIndex) (node : TreeNode) (position : Nat) (maximum : Option BorTag)
    (kind : AccessKind) (removed : List UniIndex)
    (legal : Removal tree location after maximum kind removed) :
    Removal tree location before maximum kind removed ∧
      residualRelation tree location after root query node maximum kind position removed =
      residualRelation tree location before root query node maximum kind position removed :=
  ⟨removal tree location before after same maximum kind removed legal,
    by simp only [residualRelation,count_eq tree location before after same]⟩

/-- Full nested-mask callback authorization weakens whenever exposed-node
protector membership stays equal. No exact permission profile is involved. -/
theorem authorization (tree : BorrowTree) (location : LocationTree) (before after : ProtectedTags)
    (weaken : ∀ tag, after.contains tag = true → before.contains tag = true)
    (same : ∀ index node, tree.nodeAt index = some node → node.isExposed = true → after.contains node.tag = before.contains node.tag)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop)
    (old : DuplicatePrefixResidualWriteRepaired.Authorization tree location before root position maximum kind support) :
    DuplicatePrefixResidualWriteRepaired.Authorization tree location after root position maximum kind support := by
  refine ⟨old.rooted,old.present,old.children,old.covers,old.possible,?_,?_⟩
  · intro first second legalFirst legalSecond subset index node inside present retained
    have relationEq (removed : List UniIndex) : residualRelation tree location after root index node maximum kind position removed =
        residualRelation tree location before root index node maximum kind position removed := by
      simp only [residualRelation,count_eq tree location before after same]
    rw [relationEq first,relationEq second]
    exact authorized _ kind _ _ (weaken node.tag) _ _
      (old.queries first second (removal tree location before after same maximum kind first legalFirst)
        (removal tree location before after same maximum kind second legalSecond) subset index node inside present retained)
  · intro primary
    obtain ⟨index,node,inside,present,supported⟩ := old.witness primary
    refine ⟨index,node,inside,present,?_⟩
    simpa only [Supports,same index node present supported.1] using supported

end DuplicatePrefix.CurrentCallEmptyEntryRepairedProtectorDrop

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryRepairedProtectorDrop" then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved repaired protector dependency {dependency}"
