import duplicate_prefix.GeneralBorrowSharedGeneratorProfile
import duplicate_prefix.GeneralBorrowSifaExactReadFrame
import duplicate_prefix.GeneralBorrowFullSharedFormation
namespace DuplicatePrefix.GeneralBorrowFullSharedAppend
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowSharedGeneratorProfile
open DuplicatePrefix.GeneralBorrowFreshAnchor DuplicatePrefix.GeneralBorrowFreshGraph
open DuplicatePrefix.GeneralBorrowFreshMaterialization DuplicatePrefix.GeneralBorrowFreshLocation
open DuplicatePrefix.GeneralBorrowView DuplicatePrefix.RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

private theorem full_locations (input : GeneralBorrowFreshMetadataChildShared.Input)
    (location : LocationTree) (offset : input.offset = 0)
    (initial : input.tree.locations = homogeneous input.len location) :
    GeneralBorrowFreshMetadataChildShared.locations input = homogeneous input.len (materialized location (index input) sharedState) := by
  dsimp only [GeneralBorrowFreshMetadataChildShared.locations]
  rw [offset,initial]
  have exactState := GeneralBorrowFreshModify.state_exact (homogeneous input.len location)
    (Size.ofBytes 0) (Size.ofBytes input.len) (fun _ current => materialized current (index input) sharedState)
    (by simp [homogeneous,DedupRangeMap.WellFormed,UInt64.pos_iff_ne_zero.mpr input.nonzero]) (by simp [homogeneous, Size.ofBytes, DedupRangeMap.size])
  have zero : Size.ofBytes 0 = Size.ZERO := rfl
  rw [zero] at exactState ⊢
  rw [iter_mut_homogeneous_full input.len location input.nonzero] at exactState
  rw [exactState]
  simp [GeneralBorrowFreshModify.atPosition,homogeneous]


private theorem homogeneous_exact (capacity : UInt64) (tree : BorrowTree) (location : LocationTree) (query : UniIndex)
    (expected : Option LocationState) (locations : tree.locations = homogeneous capacity location)
    (stored : location.perms.get query = expected) :
    GeneralBorrowSifaExactReadFrame.ExactAt tree query expected := by
  intro position valid
  have zero : position = 0 := by
    have bound : position < 1 := by simpa only [locations,homogeneous,Array.size_singleton] using valid
    omega
  subst position
  simpa only [locations,homogeneous,Array.getElem_singleton] using stored

private theorem result_exact (input : Input) (location postLocation : LocationTree)
    (offset : input.offset = 0)
    (initial : input.tree.locations = homogeneous input.len location)
    (final : (result input).locations = homogeneous input.len postLocation)
    (query : UniIndex) (expected : Option LocationState)
    (stable : ∀ state, expected = some state →
      {state with idempotentForeignAccess := (state.idempotentForeignAccess.ensureNoStrongerThan .Read).1} = state)
    (stored : (materialized location (index input) sharedState).perms.get query = expected) :
    postLocation.perms.get query = expected := by
  have staged : (stage input).locations = homogeneous input.len (materialized location (index input) sharedState) :=
    full_locations input location offset initial
  have exactState := GeneralBorrowSifaExactReadFrame.sifa_exact (stage input) input.parent query expected stable
    (homogeneous_exact input.len (stage input) _ query expected staged stored)
  rw [←tree_eq input] at exactState
  simpa only [final,homogeneous,Array.getElem_singleton] using exactState 0 (by simp [final,homogeneous])

private theorem stable_unique (state : LocationState)
    (same : some GeneralBorrowWildcardLeaf.unique = some state) :
    {state with idempotentForeignAccess := (state.idempotentForeignAccess.ensureNoStrongerThan .Read).1} = state := by
  cases same
  rfl

private theorem stable_shared (state : LocationState) (same : some sharedState = some state) :
    {state with idempotentForeignAccess := (state.idempotentForeignAccess.ensureNoStrongerThan .Read).1} = state := by
  cases same
  rfl

attribute [local irreducible] GeneralBorrowFreshMetadataChildShared.result GeneralBorrowFreshMetadataChildShared.stage

/-- The actual full-slice shared append preserves the complete exact generator
profile, including every sparse vacancy. Constructor success and all poststate
permissions are derived from initial graph/profile data. -/
theorem append (input : Input) (location : LocationTree)
    (offset : input.offset = 0)
    (initial : input.tree.locations = homogeneous input.len location)
    (parentless : input.parentNode.parent = none)
    (profile : Profile input.tree location input.parent) :
    ∃ postLocation, (result input).locations = homogeneous input.len postLocation ∧
      Profile (result input) postLocation input.parent ∧ postLocation.exposedCache = location.exposedCache := by
  obtain ⟨postLocation,root,node,final,ready,cache⟩ :=
    GeneralBorrowFullSharedFormation.append_ready input location offset initial parentless
  have notNew : input.parent ≠ index input := GeneralBorrowFreshNode.parent_not_fresh
    input.tree.nodes (index input) input.parent input.parentNode (at_end input) input.parentPresent
  have lookup : ∀ query, query ≠ input.parent → query ≠ index input →
      (result input).nodeAt query = none → input.tree.nodeAt query = none := by
    intro query notParent notIndex absent
    have stagedOther : (stage input).nodeAt query = input.tree.nodeAt query := by
      simpa only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt] using
        GeneralBorrowFreshGraph.other_lookup input.tree (index input) input.parent query input.parentNode
          (sharedNode input.newTag input.parent) (at_end input) input.parentPresent notParent notIndex
    have shaped := GeneralBorrowFreshMetadata.lookup_shape (stage input) (result input) (shape input) query
    rw [show (result input).nodes.get query = none from absent,show (stage input).nodes.get query = input.tree.nodeAt query from stagedOther] at shaped
    cases old : input.tree.nodeAt query with
    | none => rfl
    | some oldNode => simp [old] at shaped
  refine ⟨postLocation,final,⟨?_,?_,?_⟩,cache⟩
  · apply result_exact input location postLocation offset initial final input.parent
      (some GeneralBorrowWildcardLeaf.unique) stable_unique
    exact (get_other location.perms (index input) input.parent sharedState notNew).trans profile.rootStored
  · intro query queryNode present different
    apply result_exact input location postLocation offset initial final query (some sharedState) stable_shared
    by_cases newIndex : query = index input
    · subst query
      exact get_same location.perms (index input) sharedState
    · rw [show (materialized location (index input) sharedState).perms.get query = location.perms.get query from
        get_other location.perms (index input) query sharedState newIndex]
      have stagedOther : (stage input).nodeAt query = input.tree.nodeAt query := by
        simpa only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt] using
          GeneralBorrowFreshGraph.other_lookup input.tree (index input) input.parent query input.parentNode
            (sharedNode input.newTag input.parent) (at_end input) input.parentPresent different newIndex
      obtain ⟨oldNode,oldPresent,_⟩ := GeneralBorrowFreshMetadata.node_exists (result input) (stage input)
        (shape input).symm query queryNode present
      exact profile.shared query oldNode (stagedOther.symm.trans oldPresent) different
  · intro query absent
    have notParent : query ≠ input.parent := by
      intro same
      subst query
      rw [show (result input).nodes.get input.parent = some root from ready.rootPresent] at absent
      cases absent
    have notIndex : query ≠ index input := by
      intro same
      subst query
      rw [show (result input).nodes.get (index input) = some node from ready.present] at absent
      cases absent
    apply result_exact input location postLocation offset initial final query none (by intro state impossible;cases impossible)
    exact (get_other location.perms (index input) query sharedState notIndex).trans
      (profile.vacant query (lookup query notParent notIndex absent))
end DuplicatePrefix.GeneralBorrowFullSharedAppend
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowFullSharedAppend.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved shared append profile dependency {dependency}"

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowFullSharedAppend.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved full-slice constructor dependency {dependency}"
