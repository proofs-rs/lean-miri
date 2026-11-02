import duplicate_prefix.GeneralBorrowSharedGeneratorProfile
import duplicate_prefix.GeneralBorrowSifaExactReadFrame
import duplicate_prefix.GeneralBorrowFreshMetadataChildSharedReuse
import duplicate_prefix.GeneralBorrowSifaCacheFrame
import duplicate_prefix.GeneralBorrowFreshModify
namespace DuplicatePrefix.GeneralBorrowFullSharedReuseProfile
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshMetadataChildSharedReuse DuplicatePrefix.GeneralBorrowSharedGeneratorProfile
open DuplicatePrefix.GeneralBorrowFreshAnchor DuplicatePrefix.GeneralBorrowFreshGraph
open DuplicatePrefix.GeneralBorrowFreshMaterialization DuplicatePrefix.GeneralBorrowFreshLocation
open DuplicatePrefix.GeneralBorrowView DuplicatePrefix.RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

private theorem map_ext {α : Type} (left right : DedupRangeMap α) (same : left.entries = right.entries) : left = right := by
  cases left;cases right;cases same;rfl

private theorem segment_ext {α : Type} (left right : RangeMapSegment α)
    (range : left.range = right.range) (data : left.data = right.data) : left = right := by
  cases left;cases right;cases range;cases data;rfl

private theorem map_get {α β : Type} (shape : α → β) (nodes : UniValMap α) (query : UniIndex) :
    (⟨nodes.data.map (Option.map shape)⟩ : UniValMap β).get query = (nodes.get query).map shape := by
  unfold UniValMap.get
  simp only [Array.getElem?_map]
  cases cell : nodes.data[query.toNat]? with
  | none => rfl
  | some entry => cases entry <;> rfl

private theorem shape_homogeneous (capacity : UInt64) (before after : BorrowTree) (location : LocationTree)
    (same : treeShape after = treeShape before) (initial : before.locations = homogeneous capacity location) :
    ∃ next, after.locations = homogeneous capacity next ∧ locationShape next = locationShape location := by
  have rows := congrArg (fun shape => shape.2.2.1) same
  change after.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
    before.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) at rows
  rw [initial] at rows
  have size : after.locations.entries.size = 1 := by
    have sizes := congrArg Array.size rows
    simpa [homogeneous] using sizes
  have valid : 0 < after.locations.entries.size := by rw [size];decide
  let next := (after.locations.entries[0]'valid).data
  have entry : ((after.locations.entries[0]'valid).range,locationShape next) = (⟨0,capacity⟩,locationShape location) := by
    have known := congrArg (fun entries => entries[0]?) rows
    simpa [homogeneous,Array.getElem?_eq_getElem valid,next] using known
  have entryEq : (after.locations.entries[0]'valid) = ⟨⟨0,capacity⟩,next⟩ :=
    segment_ext _ _ (congrArg Prod.fst entry) rfl
  refine ⟨next,?_,congrArg Prod.snd entry⟩
  apply map_ext
  apply Array.ext
  · simpa [homogeneous] using size
  · intro i left right
    have zero : i = 0 := by omega
    subst i
    simpa [homogeneous] using entryEq


private theorem full_locations (input : GeneralBorrowFreshMetadataChildSharedReuse.Input)
    (location : LocationTree) (offset : input.offset = 0)
    (initial : input.tree.locations = homogeneous input.len location) :
    GeneralBorrowFreshMetadataChildSharedReuse.locations input = homogeneous input.len (materialized location (index input) sharedState) := by
  dsimp only [GeneralBorrowFreshMetadataChildSharedReuse.locations]
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

attribute [local irreducible] GeneralBorrowFreshMetadataChildSharedReuse.result GeneralBorrowFreshMetadataChildSharedReuse.stage

/-- The actual full-slice shared vacant-slot reuse preserves the complete exact generator
profile, including every sparse vacancy. Constructor success and all poststate
permissions are derived from initial graph/profile data. -/
theorem reuse (input : Input) (location : LocationTree)
    (offset : input.offset = 0)
    (initial : input.tree.locations = homogeneous input.len location)
    (profile : Profile input.tree location input.parent) :
    ∃ postLocation, (result input).locations = homogeneous input.len postLocation ∧
      Profile (result input) postLocation input.parent ∧ postLocation.exposedCache = location.exposedCache := by
  have installed : (stage input).locations = homogeneous input.len (materialized location (index input) sharedState) := by
    unfold GeneralBorrowFreshMetadataChildSharedReuse.stage GeneralBorrowFreshMetadataChildAttach.staged
    exact full_locations input location offset initial
  obtain ⟨postLocation,final,postShape⟩ := shape_homogeneous input.len (stage input) (result input)
    (materialized location (index input) sharedState) (shape input) installed
  have output := GeneralBorrowFreshMetadataChildSharedReuse.reuse input
  obtain ⟨node,nodePresent,nodeFacts⟩ := output.newNode
  have rootStage : (stage input).nodeAt input.parent = some (updatedParent input.parentNode (index input)) := by
    simpa only [GeneralBorrowFreshMetadataChildSharedReuse.stage,GeneralBorrowFreshMetadataChildAttach.staged,
      GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt] using
      GeneralBorrowFreshMetadataChildReuseGraph.parent_lookup input.tree (index input) input.parent input.parentNode
        (sharedNode input.newTag input.parent) input.vacant input.parentPresent
  obtain ⟨root,rootPresent,rootFacts⟩ := GeneralBorrowFreshMetadata.node_fields
    (stage input) (result input) (shape input) input.parent (updatedParent input.parentNode (index input)) rootStage
  have caches := GeneralBorrowSifaCacheFrame.sifa_cache (stage input) input.parent .Read
  rw [←tree_eq input] at caches
  dsimp only [GeneralBorrowSifaCacheFrame.cacheShape] at caches
  rw [final,installed] at caches
  have cache : postLocation.exposedCache = location.exposedCache := by
    simpa [homogeneous,materialized] using caches
  have notNew : input.parent ≠ index input := GeneralBorrowFreshReuseNode.parent_not_vacant
    input.tree.nodes (index input) input.parent input.parentNode input.vacant input.parentPresent
  have lookup : ∀ query, query ≠ input.parent → query ≠ index input →
      (result input).nodeAt query = none → input.tree.nodeAt query = none := by
    intro query notParent notIndex absent
    have stagedOther : (stage input).nodeAt query = input.tree.nodeAt query := by
      simpa only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt] using
        GeneralBorrowFreshMetadataChildReuseGraph.other_lookup input.tree (index input) input.parent query input.parentNode
          (sharedNode input.newTag input.parent) input.vacant input.parentPresent notParent notIndex
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
          GeneralBorrowFreshMetadataChildReuseGraph.other_lookup input.tree (index input) input.parent query input.parentNode
            (sharedNode input.newTag input.parent) input.vacant input.parentPresent different newIndex
      obtain ⟨oldNode,oldPresent,_⟩ := GeneralBorrowFreshMetadata.node_exists (result input) (stage input)
        (shape input).symm query queryNode present
      exact profile.shared query oldNode (stagedOther.symm.trans oldPresent) different
  · intro query absent
    have notParent : query ≠ input.parent := by
      intro same
      subst query
      rw [show (result input).nodes.get input.parent = some root from rootPresent] at absent
      cases absent
    have notIndex : query ≠ index input := by
      intro same
      subst query
      rw [show (result input).nodes.get (index input) = some node from nodePresent] at absent
      cases absent
    apply result_exact input location postLocation offset initial final query none (by intro state impossible;cases impossible)
    exact (get_other location.perms (index input) query sharedState notIndex).trans
      (profile.vacant query (lookup query notParent notIndex absent))
end DuplicatePrefix.GeneralBorrowFullSharedReuseProfile
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowFullSharedReuseProfile.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved shared reuse profile dependency {dependency}"
