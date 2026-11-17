import duplicate_prefix.DuplicatePrefixCallbackVisitAuthorization
import duplicate_prefix.GeneralBorrowExposedConditionalReadPermissions
import duplicate_prefix.GeneralBorrowExposedNonleafCoherence

namespace DuplicatePrefix.GeneralBorrowSnapshotReadState
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization
open GeneralBorrowWildcardVirtualLeaf (effective materialized)
open GeneralBorrowExposedNonleafState (ReadFrame updated updated_other updated_frame)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- Read classification depends only on Read counters, even when a real Read
changes Write exposure levels and Write counters. No complete-cache equality
or zero/nonzero permission profile is required. -/
theorem relation_frame (before after : LocationTree) (frame : ReadFrame before after)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (rootPosition : Nat) :
    relation after root index node maximum .Read rootPosition =
      relation before root index node maximum .Read rootPosition := by
  have counts (query : UniIndex) : GeneralBorrowWildcardRelatednessBounds.count after.exposedCache query .Read =
      GeneralBorrowWildcardRelatednessBounds.count before.exposedCache query .Read :=
    congrArg UInt16.toNat (frame query)
  simp only [relation, counts]

private theorem allows_read (level : WildcardAccessLevel) :
    GeneralBorrowExposureCardinality.supports level .Read = level.allows .Read := by
  cases level <;> rfl

/-- Effective-state framing and Read-counter framing transport the FULL raw
snapshot, including the physical-root supporting witness. -/
theorem snapshot_frame (tree : BorrowTree) (before after : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (snapshot : Snapshot tree before protections root rootPosition maximum .Read support)
    (frame : ReadFrame before after)
    (same : ∀ query node, tree.nodes.get query = some node → effective after query node = effective before query node) :
    Snapshot tree after protections root rootPosition maximum .Read support := by
  refine ⟨?_, ?_⟩
  · intro query node included present
    rw [relation_frame before after frame]
    change Scalar (effective after query node) .Read _ _
    rw [same query node present]
    exact snapshot.scalar query node included present
  · intro physical
    obtain ⟨index,node,included,present,witness⟩ := snapshot.witness physical
    refine ⟨index,node,included,present,?_⟩
    change node.isExposed = true ∧
      ((effective after index node).permission.strongestAllowedLocalAccess (protections.contains node.tag)).allows .Read = true ∧ _
    rw [same index node present]
    exact witness

theorem materialized_snapshot (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (snapshot : Snapshot tree location protections root rootPosition maximum .Read support)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node) :
    Snapshot tree (materialized location index node) protections root rootPosition maximum .Read support :=
  snapshot_frame tree location _ protections root rootPosition maximum support snapshot (fun _ => rfl)
    (GeneralBorrowExposedVirtualSchedule.materialized_effective tree location index node present)

def wildcard : AccessRelatedness → WildcardAccessRelatedness
  | .LocalAccess => .LocalAccess
  | .ForeignAccess => .ForeignAccess

/-- A real successful Read's node/cache write-back retains the full raw
snapshot. Successful scalar equations are supplied by post below; this helper
only transports their source-derived endpoint and unchanged Read support. -/
theorem updated_snapshot (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (snapshot : Snapshot tree location protections root rootPosition maximum .Read support)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (exact : AccessRelatedness) (recorded next : LocationState) (delta : PermTransition)
    (frame : ReadFrame location (updated tree location index node protections recorded next delta))
    (related : relation location root index node maximum .Read rootPosition = some (wildcard exact))
    (compatible : GeneralBorrowProtectedReadCompatible.Compatible next exact (protections.contains node.tag))
    (readSupport : GeneralBorrowExposureCardinality.supports
      (next.permission.strongestAllowedLocalAccess (protections.contains node.tag)) .Read =
      GeneralBorrowExposureCardinality.supports
        ((effective location index node).permission.strongestAllowedLocalAccess (protections.contains node.tag)) .Read) :
    Snapshot tree (updated tree location index node protections recorded next delta)
      protections root rootPosition maximum .Read support := by
  let after := updated tree location index node protections recorded next delta
  have sameOther (query : UniIndex) (queryNode : TreeNode) (different : query ≠ index) :
      effective after query queryNode = effective location query queryNode := by
    simp only [effective, after, updated_other tree location index query node protections recorded next delta different]
  have sameIndex : effective after index node = next := by
    simp only [after, updated, effective, GeneralBorrowWildcardSubtreeState.write_same, Option.getD_some]
  refine ⟨?_, ?_⟩
  · intro query queryNode included found
    rw [relation_frame location after frame]
    by_cases same : query = index
    · subst query
      have nodeEq := Option.some.inj (present.symm.trans found)
      subst queryNode
      rw [related]
      change Scalar (effective after index node) .Read _ _
      rw [sameIndex]
      cases exact <;> exact ⟨compatible.1, Or.inr compatible⟩
    · change Scalar (effective after query queryNode) .Read _ _
      rw [sameOther query queryNode same]
      exact snapshot.scalar query queryNode included found
  · intro physical
    obtain ⟨query,queryNode,included,found,witness⟩ := snapshot.witness physical
    refine ⟨query,queryNode,included,found,?_⟩
    by_cases same : query = index
    · subst query
      have nodeEq := Option.some.inj (present.symm.trans found)
      subst queryNode
      rcases witness with ⟨exposed,allowed,cutoff⟩
      refine ⟨exposed,?_,cutoff⟩
      change ((effective after index node).permission.strongestAllowedLocalAccess (protections.contains node.tag)).allows .Read = true
      rw [sameIndex, ←allows_read, readSupport, allows_read]
      exact allowed
    · change queryNode.isExposed = true ∧
        ((effective after query queryNode).permission.strongestAllowedLocalAccess (protections.contains queryNode.tag)).allows .Read = true ∧ _
      rw [sameOther query queryNode same]
      exact witness

/-- One non-skipped postorder Read query derives its actual scalar operations
(or Either materialization), retains every raw snapshot query and the real
exposure-cache invariant, and frames all other stored node states. This is the
postorder STEP needed by a general DFS proof, not whole-callback completion.
No successful operation is an input, and no zero/nonzero permission profile,
leaf shape, root order, tag cutoff exclusion or complete-cache equality is
assumed. A physical-root witness remains data until a separate DFS path proof
establishes that the source's seen bit becomes true. -/
theorem post (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (snapshot : Snapshot tree location protections root rootPosition maximum .Read support)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (index : UniIndex) (node : TreeNode) (included : support index) (present : tree.nodes.get index = some node)
    (recurse : DuplicatePrefixCallbackVisitAuthorization.entrySkip (effective location index node) .Read
      (relation location root index node maximum .Read rootPosition) = false) :
    ∃ after,
      ((relation location root index node maximum .Read rootPosition = some .EitherAccess ∧ after = materialized location index node) ∨
       ∃ exact recorded next delta,
         relation location root index node maximum .Read rootPosition = some (wildcard exact) ∧
         (effective location index node).recordNewAccess .Read exact = .Recorded recorded ∧
         recorded.performAccess .Read exact (protections.contains node.tag) = .Success next delta ∧
         after = updated tree location index node protections recorded next delta) ∧
      Snapshot tree after protections root rootPosition maximum .Read support ∧
      ReadFrame location after ∧ GeneralBorrowExposureCardinality.LocationCoherent tree after protections ∧
      (∀ query, query ≠ index → after.perms.get query = location.perms.get query) := by
  have authorized := snapshot.scalar index node included present
  cases classified : relation location root index node maximum .Read rootPosition with
  | none => simp [classified, Scalar] at authorized
  | some related =>
    rw [classified] at authorized
    rw [classified] at recurse
    cases related with
    | EitherAccess =>
      refine ⟨materialized location index node, .inl ⟨rfl,rfl⟩,
        materialized_snapshot tree location protections root rootPosition maximum support snapshot index node present,
        (fun _ => rfl), GeneralBorrowExposedNonleafCoherence.materialized_coherent tree location index node protections present coherent, ?_⟩
      intro query different
      unfold materialized UniValMap.orInsert
      split
      · rfl
      · exact GeneralBorrowFreshLocation.get_other _ index query _ different
    | LocalAccess =>
      let exact : AccessRelatedness := .LocalAccess
      have skipped : skip (effective location index node) .Read exact = false := recurse
      have compatible : GeneralBorrowProtectedReadCompatible.Compatible (effective location index node) exact
          (protections.contains node.tag) := by
        rcases authorized.2 with forbidden | compatible
        · have impossible : (false : Bool) = true := skipped.symm.trans forbidden
          cases impossible
        · exact compatible
      have scheduled : (effective location index node).skipIfKnownNoop .Read exact = .Recurse := by
        cases equality : (effective location index node).skipIfKnownNoop .Read exact with
        | Recurse => rfl
        | SkipSelfAndChildren =>
          have yes := (skip_source _ _ _).mpr equality
          simp [skipped] at yes
      obtain ⟨recorded,next,delta,record,access,good,readSupport⟩ := GeneralBorrowExposedConditionalReadPermissions.visit
        (effective location index node) exact (protections.contains node.tag) compatible
        (GeneralBorrowEvents.recurse_scheduled _ _ _ scheduled)
      let after := updated tree location index node protections recorded next delta
      have frame := updated_frame tree location index node protections recorded next delta depth present readSupport
      refine ⟨after, .inr ⟨exact,recorded,next,delta,rfl,record,access,rfl⟩,
        updated_snapshot tree location protections root rootPosition maximum support snapshot index node present exact recorded next delta
          frame classified good readSupport, frame,
        GeneralBorrowExposedNonleafCoherence.updated_coherent tree location index node protections recorded next delta exact depth present coherent record access,
        ?_⟩
      exact fun query different => updated_other tree location index query node protections recorded next delta different
    | ForeignAccess =>
      let exact : AccessRelatedness := .ForeignAccess
      have skipped : skip (effective location index node) .Read exact = false := recurse
      have compatible : GeneralBorrowProtectedReadCompatible.Compatible (effective location index node) exact
          (protections.contains node.tag) := by
        rcases authorized.2 with forbidden | compatible
        · have impossible : (false : Bool) = true := skipped.symm.trans forbidden
          cases impossible
        · exact compatible
      have scheduled : (effective location index node).skipIfKnownNoop .Read exact = .Recurse := by
        cases equality : (effective location index node).skipIfKnownNoop .Read exact with
        | Recurse => rfl
        | SkipSelfAndChildren =>
          have yes := (skip_source _ _ _).mpr equality
          simp [skipped] at yes
      obtain ⟨recorded,next,delta,record,access,good,readSupport⟩ := GeneralBorrowExposedConditionalReadPermissions.visit
        (effective location index node) exact (protections.contains node.tag) compatible
        (GeneralBorrowEvents.recurse_scheduled _ _ _ scheduled)
      let after := updated tree location index node protections recorded next delta
      have frame := updated_frame tree location index node protections recorded next delta depth present readSupport
      refine ⟨after, .inr ⟨exact,recorded,next,delta,rfl,record,access,rfl⟩,
        updated_snapshot tree location protections root rootPosition maximum support snapshot index node present exact recorded next delta
          frame classified good readSupport, frame,
        GeneralBorrowExposedNonleafCoherence.updated_coherent tree location index node protections recorded next delta exact depth present coherent record access,
        ?_⟩
      exact fun query different => updated_other tree location index query node protections recorded next delta different

end DuplicatePrefix.GeneralBorrowSnapshotReadState
