import duplicate_prefix.DuplicatePrefixResidualSavedWritePost
import duplicate_prefix.GeneralBorrowSnapshotReadRuntime

namespace DuplicatePrefix.GeneralBorrowResidualWriteRuntime
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization DuplicatePrefixResidualCountModel
open GeneralBorrowWildcardVirtualLeaf (effective materialized)
open GeneralBorrowExposedNonleafState (updated updated_other)
open GeneralBorrowSnapshotReadRuntime (GlobalPossible)
open DuplicatePrefixResidualWritePost (Action)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Extraction from an already derived scalar result. Successful access checks
the resulting state's possibility bit; no ownership restriction is needed. -/
theorem access_possible (state next : LocationState) (delta : PermTransition)
    (kind : AccessKind) (exact : AccessRelatedness) (held : Bool)
    (access : state.performAccess kind exact held = .Success next delta) : next.possible = true := by
  unfold LocationState.performAccess at access
  cases performed : performAccessTransition kind exact state.permission held with
  | UndefinedBehavior => simp only [performed] at access; cases access
  | ImpossibleProtectedReservedIM => simp only [performed] at access; cases access
  | Transition transition =>
    simp only [performed] at access
    cases applied : transition.applied state.permission with
    | none => simp only [applied] at access; cases access
    | some permission =>
      simp only [applied] at access
      split at access
      · cases access
      · split at access
        · cases access
        · rename_i possible
          cases access
          simpa using possible

/-- Runtime extraction for the actual two source Write actions. The caller of
the public post theorem below obtains Action from raw authorization, never as
a final sufficient-safety premise. Materialization and exact updates preserve
all present possible states, physical SIFA consistency, and vacant entries. -/
theorem action_runtime (tree : BorrowTree) (current : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (position : Nat)
    (removed : List UniIndex) (after : LocationTree) (afterRemoved : List UniIndex)
    (present : tree.nodes.get index = some node)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree current protections)
    (possible : GlobalPossible tree current)
    (action : Action tree current protections root index node maximum position removed after afterRemoved) :
    GeneralBorrowLocationSifaConsistency.Profile tree after protections ∧
      GlobalPossible tree after ∧
      (∀ query, tree.nodes.get query = none → after.perms.get query = current.perms.get query) := by
  rcases action with ⟨_,same,_⟩ | ⟨exact,recorded,next,delta,_,record,access,same,_⟩
  · subst after
    have other : ∀ query, query ≠ index →
        (materialized current index node).perms.get query = current.perms.get query := by
      intro query different
      unfold materialized UniValMap.orInsert
      split
      · rfl
      · exact GeneralBorrowFreshLocation.get_other _ index query _ different
    refine ⟨GeneralBorrowSnapshotReadRuntime.materialized_profile tree current protections index node present profile,
      ?_, GeneralBorrowSnapshotReadRuntime.vacant_frame tree current _ index node present other⟩
    intro query queryNode found
    rw [GeneralBorrowExposedVirtualSchedule.materialized_effective tree current index node present query queryNode found]
    exact possible query queryNode found
  · subst after
    refine ⟨GeneralBorrowSnapshotReadRuntime.updated_profile tree current protections index node present
      recorded next delta .Write exact profile record access, ?_, ?_⟩
    · intro query queryNode found
      by_cases same : query = index
      · subst query
        have nodeEq : queryNode = node := Option.some.inj (found.symm.trans present)
        subst queryNode
        simpa only [effective,updated,GeneralBorrowWildcardSubtreeState.write_same,Option.getD_some] using
          access_possible recorded next delta .Write exact (protections.contains node.tag) access
      · simpa only [effective,updated_other tree current index query node protections recorded next delta same] using
          possible query queryNode found
    · exact GeneralBorrowSnapshotReadRuntime.vacant_frame tree current _ index node present
        (fun query different => updated_other tree current index query node protections recorded next delta different)

/-- Saved-entry-mask Write post processing, with its complete real action and
runtime preservation derived from raw finite authorization/model invariants.
No operation-success, ownership, leaf, ancestor or free-pool premise is added. -/
theorem post_with_runtime (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (rootPosition : Nat) (support : UniIndex → Prop)
    (authorization : Authorization tree initial protections root rootPosition maximum .Write support)
    (before removed : List UniIndex)
    (legalBefore : Removal tree initial protections maximum .Write before)
    (subset : ∀ query ∈ before, query ∈ removed)
    (legal : Removal tree initial protections maximum .Write removed)
    (matching : Matches tree initial current protections .Write removed)
    (initialCoherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (currentCoherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections)
    (short : tree.nodes.size < 65536) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree current protections)
    (possible : GlobalPossible tree current)
    (inside : support index) (present : tree.nodes.get index = some node)
    (unvisited : current.perms.get index = initial.perms.get index)
    (initialActive : DuplicatePrefixCallbackVisitAuthorization.entrySkip
      (effective initial index node) .Write (residualRelation tree initial protections root index node maximum .Write rootPosition before) = false) :
    ∃ after afterRemoved,
      Action tree current protections root index node maximum rootPosition removed after afterRemoved ∧
      Removal tree initial protections maximum .Write afterRemoved ∧
      Matches tree initial after protections .Write afterRemoved ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree after protections ∧
      (∀ query, query ≠ index → after.perms.get query = current.perms.get query) ∧
      GeneralBorrowLocationSifaConsistency.Profile tree after protections ∧
      GlobalPossible tree after ∧
      (∀ query, tree.nodes.get query = none → after.perms.get query = current.perms.get query) := by
  obtain ⟨after,afterRemoved,action,afterLegal,afterMatches,afterCoherent,other⟩ :=
    DuplicatePrefixResidualSavedWritePost.post tree initial current protections root index node maximum rootPosition support
      authorization before removed legalBefore subset legal matching initialCoherent currentCoherent short depth
      inside present unvisited initialActive
  obtain ⟨afterProfile,afterPossible,vacant⟩ := action_runtime tree current protections root index node maximum rootPosition
    removed after afterRemoved present profile possible action
  exact ⟨after,afterRemoved,action,afterLegal,afterMatches,afterCoherent,other,afterProfile,afterPossible,vacant⟩

end DuplicatePrefix.GeneralBorrowResidualWriteRuntime
