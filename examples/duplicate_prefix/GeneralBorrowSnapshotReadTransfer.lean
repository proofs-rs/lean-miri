import duplicate_prefix.GeneralBorrowSnapshotReadSupport
import duplicate_prefix.DuplicatePrefixReadWriteScalarAuthorization
namespace DuplicatePrefix.GeneralBorrowSnapshotReadTransfer
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixCallbackVisitAuthorization
open GeneralBorrowWildcardVirtualLeaf (effective materialized)
open GeneralBorrowExposedNonleafState (ReadFrame updated updated_other)
open GeneralBorrowSnapshotReadState (wildcard)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- Raw finite Read/Write query guards; Either performs no scalar Read. -/
def QueryGuards (readQuery : Option WildcardAccessRelatedness)
    (entry exit : Option WildcardAccessRelatedness) : Prop :=
  match readQuery with
  | some .LocalAccess => DuplicatePrefixReadWriteScalarAuthorization.Guards .LocalAccess entry exit
  | some .ForeignAccess => DuplicatePrefixReadWriteScalarAuthorization.Guards .ForeignAccess entry exit
  | some .EitherAccess | none => True

/-- Internal scalar transfer table over the sixteen optional Write-query pairs.
It states no operation success and is initialized by reflexivity. -/
def Transfer (readQuery : Option WildcardAccessRelatedness) (old current : LocationState) (held : Bool) : Prop :=
  ∀ entry exit, QueryGuards readQuery entry exit →
    Authorized old .Write held entry exit → Authorized current .Write held entry exit

/-- A support-wide scalar transfer invariant, indexed by the fixed original
Read cache query. It is independent of contributor-mask simulation. -/
def Global (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (support : UniIndex → Prop) : Prop :=
  ∀ index node, support index → tree.nodes.get index = some node →
    Transfer (relation initial root index node maximum .Read rootPosition)
      (effective initial index node) (effective current index node) (protections.contains node.tag)

theorem initial (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (support : UniIndex → Prop) :
    Global tree location location protections root rootPosition maximum support := by
  intro index node included present entry exit guards authorized
  exact authorized

theorem materialized_global (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (transfers : Global tree initial current protections root rootPosition maximum support)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node) :
    Global tree initial (materialized current index node) protections root rootPosition maximum support := by
  intro query queryNode included found
  change Transfer _ _ (effective (materialized current index node) query queryNode) _
  rw [GeneralBorrowExposedVirtualSchedule.materialized_effective tree current index node present query queryNode found]
  exact transfers query queryNode included found

/-- Source-derived exact Read operations preserve the global transfer table.
The original/current classification is identified by the real Read-count
frame. No initial/current scalar equality or unvisited hypothesis is needed. -/
theorem updated_global (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (snapshot : Snapshot tree current protections root rootPosition maximum .Read support)
    (frame : ReadFrame initial current)
    (transfers : Global tree initial current protections root rootPosition maximum support)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (exact : AccessRelatedness) (recorded next : LocationState) (delta : PermTransition)
    (classified : relation current root index node maximum .Read rootPosition = some (wildcard exact))
    (recurse : entrySkip (effective current index node) .Read
      (relation current root index node maximum .Read rootPosition) = false)
    (record : (effective current index node).recordNewAccess .Read exact = .Recorded recorded)
    (access : recorded.performAccess .Read exact (protections.contains node.tag) = .Success next delta) :
    Global tree initial (updated tree current index node protections recorded next delta) protections root rootPosition maximum support := by
  intro query queryNode included found
  by_cases same : query = index
  · subst query
    have nodeEq : queryNode = node := Option.some.inj (found.symm.trans present)
    subst queryNode
    have raw := snapshot.scalar index node included present
    rw [classified] at raw
    have skipFalse : skip (effective current index node) .Read exact = false := by
      rw [classified] at recurse
      cases exact <;> exact recurse
    have compatible : GeneralBorrowProtectedReadCompatible.Compatible (effective current index node) exact (protections.contains node.tag) := by
      cases exact <;> rcases raw.2 with skipped | good
      · have impossible : (false : Bool) = true := skipFalse.symm.trans skipped
        cases impossible
      · exact good
      · have impossible : (false : Bool) = true := skipFalse.symm.trans skipped
        cases impossible
      · exact good
    have scheduled : GeneralBorrowEvents.Scheduled (effective current index node) .Read exact := by
      apply GeneralBorrowEvents.recurse_scheduled
      cases skipped : (effective current index node).skipIfKnownNoop .Read exact with
      | Recurse => rfl
      | SkipSelfAndChildren =>
        have yes := (skip_source _ _ _).mpr skipped
        have impossible : (false : Bool) = true := skipFalse.symm.trans yes
        cases impossible
    have initialClassified : relation initial root index node maximum .Read rootPosition = some (wildcard exact) :=
      (GeneralBorrowSnapshotReadState.relation_frame initial current frame root index node maximum rootPosition).symm.trans classified
    intro entry exit guards authorized
    have currentAuthorized := transfers index node included present entry exit guards authorized
    have scalarGuards : DuplicatePrefixReadWriteScalarAuthorization.Guards exact entry exit := by
      rw [initialClassified] at guards
      cases exact <;> exact guards
    change Authorized (effective (updated tree current index node protections recorded next delta) index node) .Write _ entry exit
    simp only [effective,updated,GeneralBorrowWildcardSubtreeState.write_same,Option.getD_some]
    exact DuplicatePrefixReadWriteScalarAuthorization.actual_read_preserves (effective current index node) recorded next delta exact
      (protections.contains node.tag) entry exit compatible scheduled currentAuthorized scalarGuards record access
  · change Transfer _ _ (effective (updated tree current index node protections recorded next delta) query queryNode) _
    simp only [effective,updated_other tree current index query node protections recorded next delta same]
    exact transfers query queryNode included found

/-- Actual Read postorder action, with the frozen support/cache output and an
additional global finite scalar transfer table. Compatibility, scheduling and
successful operations are derived from the raw current snapshot. -/
theorem post (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (snapshot : Snapshot tree current protections root rootPosition maximum .Read support)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections)
    (initialFrame : ReadFrame initial current)
    (transfers : Global tree initial current protections root rootPosition maximum support)
    (index : UniIndex) (node : TreeNode) (included : support index) (present : tree.nodes.get index = some node)
    (recurse : entrySkip (effective current index node) .Read
      (relation current root index node maximum .Read rootPosition) = false) :
    ∃ after,
      ((relation current root index node maximum .Read rootPosition = some .EitherAccess ∧ after = materialized current index node) ∨
       ∃ exact recorded next delta,
         relation current root index node maximum .Read rootPosition = some (wildcard exact) ∧
         (effective current index node).recordNewAccess .Read exact = .Recorded recorded ∧
         recorded.performAccess .Read exact (protections.contains node.tag) = .Success next delta ∧
         after = updated tree current index node protections recorded next delta) ∧
      Snapshot tree after protections root rootPosition maximum .Read support ∧
      ReadFrame current after ∧ GeneralBorrowExposureCardinality.LocationCoherent tree after protections ∧
      (∀ query, query ≠ index → after.perms.get query = current.perms.get query) ∧
      GeneralBorrowWildcardPrimaryReadWitness.PointwiseReadFrame tree protections current after ∧
      Global tree initial after protections root rootPosition maximum support := by
  obtain ⟨after,action,afterSnapshot,frame,afterCoherent,other,pointwise⟩ :=
    GeneralBorrowSnapshotReadSupport.post_with_support tree current protections root rootPosition maximum support
      snapshot depth coherent index node included present recurse
  refine ⟨after,action,afterSnapshot,frame,afterCoherent,other,pointwise,?_⟩
  rcases action with ⟨_,same⟩ | ⟨exact,recorded,next,delta,classified,record,access,same⟩
  · subst after
    exact materialized_global tree initial current protections root rootPosition maximum support transfers index node present
  · subst after
    exact updated_global tree initial current protections root rootPosition maximum support snapshot initialFrame transfers index node present exact recorded next delta classified recurse record access
end DuplicatePrefix.GeneralBorrowSnapshotReadTransfer
