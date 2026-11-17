import duplicate_prefix.GeneralBorrowFreshRegistration
import duplicate_prefix.GeneralBorrowParentRestoreScalar
import duplicate_prefix.GeneralBorrowHiddenProtectorDropRuntime
namespace DuplicatePrefix.GeneralBorrowHiddenProtectorRowWeakens
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
open GeneralBorrowExposureCardinality
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

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

private theorem authorized (state : LocationState) (kind : AccessKind) (before after : Bool)
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

/-- Full nested-mask callback authorization weakens whenever exposed-node
protector membership stays equal. No exact permission profile is involved. -/
theorem authorization (tree : BorrowTree) (location : LocationTree) (before after : ProtectedTags)
    (weaken : ∀ tag, after.contains tag = true → before.contains tag = true)
    (same : ∀ index node, tree.nodeAt index = some node → node.isExposed = true → after.contains node.tag = before.contains node.tag)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop)
    (old : Authorization tree location before root position maximum kind support) :
    Authorization tree location after root position maximum kind support := by
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

/-- Both source Normal and every callback survive actual hidden-tag weakening. -/
theorem row (tree : BorrowTree) (location : LocationTree) (before after : ProtectedTags)
    (weaken : ∀ tag, after.contains tag = true → before.contains tag = true)
    (same : ∀ index node, tree.nodeAt index = some node → node.isExposed = true → after.contains node.tag = before.contains node.tag)
    (source selected : Option UniIndex) (maximum : Option BorTag)
    (old : DuplicatePrefixBorrowAuthorization.Row tree location before source selected maximum) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Row tree location after source selected maximum) := by
  refine ⟨{wildcard := old.wildcard,rootPath := old.rootPath,rootPresent := old.rootPresent,cutoff := old.cutoff,normal := ?_,callbacks := ?_}⟩
  · intro anchor found
    obtain ⟨normal⟩ := old.normal anchor found
    refine ⟨⟨normal.component,?_⟩⟩
    intro kind index included valid
    obtain ⟨state,present,compatible⟩ := normal.permissions kind index included valid
    exact ⟨state,present,GeneralBorrowParentRestoreScalar.weakens state kind _ _ _
      (GeneralBorrowFreshProtectorRelease.projection_weakens tree location before after weaken index) compatible⟩
  · intro position valid different
    obtain ⟨support,read,write⟩ := old.callbacks position valid different
    exact ⟨support,authorization tree location before after weaken same _ _ _ _ _ read,
      authorization tree location before after weaken same _ _ _ _ _ write⟩

/-- The complete owner window survives the same protector weakening. -/
theorem positive (tree : BorrowTree) (before after : ProtectedTags)
    (weaken : ∀ tag, after.contains tag = true → before.contains tag = true)
    (same : ∀ index node, tree.nodeAt index = some node → node.isExposed = true → after.contains node.tag = before.contains node.tag)
    (source selected : Option UniIndex) (maximum : Option BorTag) (offset len : UInt64)
    (old : DuplicatePrefixBorrowAuthorization.Positive tree before source selected maximum offset len) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive tree after source selected maximum offset len) := by
  refine ⟨{positive := old.positive,bounds := old.bounds,sourcePresent := old.sourcePresent,wildcardRoot := old.wildcardRoot,rows := ?_}⟩
  intro position valid nonempty start stop
  obtain ⟨oldRow⟩ := old.rows position valid nonempty start stop
  exact row tree _ before after weaken same source selected maximum oldRow
end DuplicatePrefix.GeneralBorrowHiddenProtectorRowWeakens
