import duplicate_prefix.DuplicatePrefixResidualWritePost
import duplicate_prefix.DuplicatePrefixWriteReadSnapshot
namespace DuplicatePrefix.DuplicatePrefixNoMaximumWriteSnapshot
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization DuplicatePrefixResidualCountModel
open GeneralBorrowWildcardVirtualLeaf (effective materialized)
open GeneralBorrowExposedNonleafState (updated updated_other)
open GeneralBorrowSnapshotReadState (wildcard)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

private theorem supports_allows (level : WildcardAccessLevel) : GeneralBorrowExposureCardinality.supports level .Write = level.allows .Write := by cases level <;> rfl

theorem successor (state recorded next : LocationState) (delta : PermTransition) (exact : AccessRelatedness) (held : Bool)
    (possible : state.possible = true)
    (record : state.recordNewAccess .Write exact = .Recorded recorded)
    (access : recorded.performAccess .Write exact held = .Success next delta) :
    GeneralBorrowExposedConditionalWritePermissions.Compatible next exact held := by
  have recordedPossible : recorded.possible = true := by
    unfold LocationState.recordNewAccess at record
    split at record
    · cases record;exact possible
    · cases record
  have compatible := (DuplicatePrefixScalarAuthorization.compatible_iff recorded .Write exact held recordedPossible).mpr ⟨next,delta,access⟩
  obtain ⟨actual,transition,performed,good,_,_⟩ := GeneralBorrowExposedConditionalWritePermissions.transition recorded exact held compatible
  have same : actual = next := (LocationState.AccessResult.Success.inj (performed.symm.trans access)).1
  simpa only [same] using good

/-- Empty legal masks yield both actual Write-query equality and exposed
Write-support equality. Read counters may change. -/
theorem frames (tree : BorrowTree) (initial current after : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat)
    (removed afterRemoved : List UniIndex)
    (legal : Removal tree initial protections none .Write removed) (afterLegal : Removal tree initial protections none .Write afterRemoved)
    (matching : Matches tree initial current protections .Write removed) (afterMatching : Matches tree initial after protections .Write afterRemoved)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections)
    (afterCoherent : GeneralBorrowExposureCardinality.LocationCoherent tree after protections) (short : tree.nodes.size < 65536) :
    (∀ index node, relation after root index node none .Write position = relation current root index node none .Write position) ∧
    (∀ index node, tree.nodes.get index = some node → node.isExposed = true →
      (GeneralBorrowExposureCardinality.effective after protections index node).allows .Write =
      (GeneralBorrowExposureCardinality.effective current protections index node).allows .Write) := by
  have empty := no_maximum_removal_empty tree initial protections .Write removed legal
  have afterEmpty := no_maximum_removal_empty tree initial protections .Write afterRemoved afterLegal
  subst removed;subst afterRemoved
  constructor
  · intro index node
    rw [relation_matches tree initial after protections .Write [] afterMatching afterCoherent short root index node none position,
      relation_matches tree initial current protections .Write [] matching coherent short root index node none position]
  · intro index node present exposed
    have old := matching index node present exposed
    have next := afterMatching index node present exposed
    have equal := next.trans old.symm
    simpa only [levels,List.contains_nil,Bool.false_eq_true,ite_false,supports_allows] using equal

theorem preserves (tree : BorrowTree) (current after : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (position : Nat) (support : UniIndex → Prop)
    (removed afterRemoved : List UniIndex)
    (snapshot : Snapshot tree current protections root position maximum .Write support)
    (present : tree.nodes.get index = some node) (included : support index)
    (action : DuplicatePrefixResidualWritePost.Action tree current protections root index node maximum position removed after afterRemoved)
    (queries : ∀ query queryNode, relation after root query queryNode maximum .Write position = relation current root query queryNode maximum .Write position)
    (supportFrame : ∀ query queryNode, tree.nodes.get query = some queryNode → queryNode.isExposed = true →
      (GeneralBorrowExposureCardinality.effective after protections query queryNode).allows .Write =
      (GeneralBorrowExposureCardinality.effective current protections query queryNode).allows .Write) :
    Snapshot tree after protections root position maximum .Write support := by
  refine ⟨?_,?_⟩
  · intro query queryNode inside found
    rw [queries]
    rcases action with ⟨_,same,_⟩ | ⟨exact,recorded,next,delta,classified,record,access,same,_⟩
    · subst after
      change DuplicatePrefixCallbackAuthorization.Scalar (effective (materialized current index node) query queryNode) .Write _ _
      rw [GeneralBorrowExposedVirtualSchedule.materialized_effective tree current index node present query queryNode found]
      exact snapshot.scalar query queryNode inside found
    · subst after
      by_cases equal : query = index
      · subst query
        have nodeEq := Option.some.inj (present.symm.trans found)
        subst queryNode
        have possible := DuplicatePrefixResidualSupportSnapshotBridge.scalar_possible _ .Write _ _ (snapshot.scalar index node included present)
        have compatible := successor (effective current index node) recorded next delta exact (protections.contains node.tag) possible record access
        rw [classified]
        change DuplicatePrefixCallbackAuthorization.Scalar (effective (updated tree current index node protections recorded next delta) index node) .Write _ _
        simp only [effective,updated,GeneralBorrowWildcardSubtreeState.write_same,Option.getD_some]
        cases exact <;> exact ⟨compatible.1,.inr compatible⟩
      · simpa only [effective,updated_other tree current index query node protections recorded next delta equal] using snapshot.scalar query queryNode inside found
  · intro physical
    obtain ⟨query,queryNode,inside,found,eligible⟩ := snapshot.witness physical
    refine ⟨query,queryNode,inside,found,eligible.1,?_,eligible.2.2⟩
    change (GeneralBorrowExposureCardinality.effective after protections query queryNode).allows .Write = true
    rw [supportFrame query queryNode found eligible.1]
    exact eligible.2.1

/-- A no-maximum actual post step retains the full Write snapshot. All real
operations come from the raw authorization-derived frozen post theorem. -/
theorem post (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (position : Nat) (support : UniIndex → Prop)
    (noMaximum : maximum = none)
    (authorization : Authorization tree initial protections root position maximum .Write support)
    (snapshot : Snapshot tree current protections root position maximum .Write support)
    (removed : List UniIndex) (legal : Removal tree initial protections maximum .Write removed)
    (matching : Matches tree initial current protections .Write removed)
    (initialCoherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections)
    (short : tree.nodes.size < 65536) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (inside : support index) (present : tree.nodes.get index = some node)
    (unvisited : current.perms.get index = initial.perms.get index)
    (active : DuplicatePrefixCallbackVisitAuthorization.entrySkip (effective initial index node) .Write
      (relation initial root index node maximum .Write position) = false) :
    ∃ after afterRemoved,
      DuplicatePrefixResidualWritePost.Action tree current protections root index node maximum position removed after afterRemoved ∧
      Removal tree initial protections maximum .Write afterRemoved ∧ Matches tree initial after protections .Write afterRemoved ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree after protections ∧
      (∀ query, query ≠ index → after.perms.get query = current.perms.get query) ∧
      Snapshot tree after protections root position maximum .Write support := by
  obtain ⟨after,afterRemoved,action,afterLegal,afterMatching,afterCoherent,other⟩ :=
    DuplicatePrefixResidualWritePost.post tree initial current protections root index node maximum position support authorization removed legal matching
      initialCoherent coherent short depth inside present unvisited active
  refine ⟨after,afterRemoved,action,afterLegal,afterMatching,afterCoherent,other,?_⟩
  subst maximum
  obtain ⟨queryFrame,supportFrame⟩ := frames tree initial current after protections root position removed afterRemoved legal afterLegal matching afterMatching coherent afterCoherent short
  exact preserves tree current after protections root index node none position support removed afterRemoved snapshot present inside action queryFrame supportFrame
end DuplicatePrefix.DuplicatePrefixNoMaximumWriteSnapshot
