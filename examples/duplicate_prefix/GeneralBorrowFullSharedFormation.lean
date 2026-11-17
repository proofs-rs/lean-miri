import duplicate_prefix.GeneralBorrowExposeReadFold
import duplicate_prefix.GeneralBorrowFreshMetadataChildShared
import duplicate_prefix.GeneralBorrowFreshInstallation
import duplicate_prefix.GeneralBorrowSifaCacheFrame

namespace DuplicatePrefix.GeneralBorrowFullSharedFormation
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposeReadFold DuplicatePrefix.GeneralBorrowFreshMetadataChildShared
open DuplicatePrefix.GeneralBorrowFreshAnchor DuplicatePrefix.GeneralBorrowFreshGraph
open DuplicatePrefix.GeneralBorrowFreshMaterialization DuplicatePrefix.GeneralBorrowFreshMetadata
open DuplicatePrefix.GeneralBorrowFreshLocation DuplicatePrefix.GeneralBorrowView DuplicatePrefix.RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

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

/-- The SIFA permission view preserves a homogeneous range and its stored
permission/accessed shape; the resulting LocationTree need not be identical. -/
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

private theorem frozen_of_shape (before after : LocationTree) (query : UniIndex)
    (shape : locationShape after = locationShape before)
    (frozen : ∃ state, before.perms.get query = some state ∧ state.permission = .Frozen) :
    ∃ state, after.perms.get query = some state ∧ state.permission = .Frozen := by
  obtain ⟨old,stored,permission⟩ := frozen
  have lookups := congrArg (fun entries => (⟨entries⟩ : UniValMap StateShape).get query) shape
  dsimp only [locationShape] at lookups
  rw [map_get,map_get,stored] at lookups
  cases found : after.perms.get query with
  | none => simp [found] at lookups
  | some state =>
    have equal : stateShape state = stateShape old := by simpa [found] using lookups
    exact ⟨state,rfl,(congrArg Prod.fst equal).trans permission⟩

private theorem staged_locations (input : GeneralBorrowFreshMetadataChildShared.Input)
    (location : LocationTree) (offset : input.offset = 0)
    (initial : input.tree.locations = homogeneous input.len location) :
    (stage input).locations = homogeneous input.len (materialized location (index input) sharedState) := by
  change GeneralBorrowFreshMetadataChildShared.locations input = _
  exact full_locations input location offset initial

/-- One actual shared newChild, including its actual SIFA result, forms raw
exposure Ready data. Only initial graph/allocator/range data are supplied.
This constructor result is not a proof of a complete retag or Rust history. -/
theorem append_ready (input : GeneralBorrowFreshMetadataChildShared.Input)
    (location : LocationTree) (offset : input.offset = 0)
    (initial : input.tree.locations = homogeneous input.len location)
    (parentless : input.parentNode.parent = none) :
    ∃ postLocation postRoot requestNode,
      (result input).locations = homogeneous input.len postLocation ∧
      Ready (result input) postLocation input.parent postRoot ⟨input.newTag,index input,requestNode⟩ ∧
      postLocation.exposedCache = location.exposedCache := by
  let after := result input
  have output := GeneralBorrowFreshMetadataChildShared.append input
  have atEnd := GeneralBorrowFreshMetadataChildShared.at_end input
  have installed := staged_locations input location offset initial
  obtain ⟨postLocation,postLocations,postShape⟩ := shape_homogeneous input.len (stage input) after
    (materialized location (index input) sharedState) (shape input) installed
  have rootStage : (stage input).nodeAt input.parent = some (updatedParent input.parentNode (index input)) := by
    simpa only [GeneralBorrowFreshMetadataChildShared.stage,GeneralBorrowFreshMetadataChildAttach.staged,
      GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt] using
      GeneralBorrowFreshGraph.parent_lookup input.tree (index input) input.parent input.parentNode
        (sharedNode input.newTag input.parent) atEnd input.parentPresent
  obtain ⟨postRoot,rootPresent,_,rootParent,_,_⟩ := GeneralBorrowFreshMetadata.node_fields
    (stage input) after (shape input) input.parent (updatedParent input.parentNode (index input)) rootStage
  obtain ⟨node,present,tag,parent,children,permission,unexposed⟩ := output.newNode
  have different : input.parent ≠ index input := by
    intro same
    have valid := GeneralBorrowNodeUpdate.lookup_valid input.tree.nodes input.parent input.parentNode input.parentPresent
    rw [same,atEnd] at valid
    omega
  have frozen : ∃ state, postLocation.perms.get (index input) = some state ∧ state.permission = .Frozen := by
    apply frozen_of_shape _ _ _ postShape
    exact ⟨sharedState,GeneralBorrowFreshLocation.get_same location.perms (index input) sharedState,rfl⟩
  have caches := GeneralBorrowSifaCacheFrame.sifa_cache (stage input) input.parent .Read
  rw [←tree_eq input] at caches
  dsimp only [GeneralBorrowSifaCacheFrame.cacheShape] at caches
  rw [postLocations,installed] at caches
  have cacheEq : postLocation.exposedCache = location.exposedCache := by
    simpa [homogeneous,materialized] using caches
  refine ⟨postLocation,postRoot,node,postLocations,?_,cacheEq⟩
  exact ⟨output.freshLookup,present,rootPresent,different,parent,rootParent.trans parentless,unexposed,frozen⟩


end DuplicatePrefix.GeneralBorrowFullSharedFormation

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowFullSharedFormation.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved full-slice constructor dependency {dependency}"
