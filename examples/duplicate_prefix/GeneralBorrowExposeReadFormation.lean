import duplicate_prefix.GeneralBorrowExposeReadFold
import duplicate_prefix.GeneralBorrowFreshMetadataChildShared
import duplicate_prefix.GeneralBorrowFreshInstallation
import duplicate_prefix.GeneralBorrowSifaCacheFrame

namespace DuplicatePrefix.GeneralBorrowExposeReadFormation
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
    (location : LocationTree) (offset : input.offset = 0) (length : input.len = 1)
    (initial : input.tree.locations = homogeneous 1 location) :
    GeneralBorrowFreshMetadataChildShared.locations input = homogeneous 1 (materialized location (index input) sharedState) := by
  dsimp only [GeneralBorrowFreshMetadataChildShared.locations]
  rw [offset,length,initial]
  have exactState := GeneralBorrowFreshModify.state_exact (homogeneous (1 : UInt64) location)
    (Size.ofBytes 0) (Size.ofBytes 1) (fun _ current => materialized current (index input) sharedState)
    (by simp [homogeneous,DedupRangeMap.WellFormed]) (by simp [homogeneous, Size.ofBytes, DedupRangeMap.size])
  have zero : Size.ofBytes 0 = Size.ZERO := rfl
  rw [zero] at exactState ⊢
  rw [iter_mut_homogeneous_full (1 : UInt64) location (by decide)] at exactState
  rw [exactState]
  simp [GeneralBorrowFreshModify.atPosition,homogeneous]

/-- The SIFA permission view preserves a homogeneous range and its stored
permission/accessed shape; the resulting LocationTree need not be identical. -/
private theorem shape_homogeneous (before after : BorrowTree) (location : LocationTree)
    (same : treeShape after = treeShape before) (initial : before.locations = homogeneous 1 location) :
    ∃ next, after.locations = homogeneous 1 next ∧ locationShape next = locationShape location := by
  have rows := congrArg (fun shape => shape.2.2.1) same
  change after.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
    before.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) at rows
  rw [initial] at rows
  have size : after.locations.entries.size = 1 := by
    have sizes := congrArg Array.size rows
    simpa [homogeneous] using sizes
  have valid : 0 < after.locations.entries.size := by rw [size];decide
  let next := (after.locations.entries[0]'valid).data
  have entry : ((after.locations.entries[0]'valid).range,locationShape next) = (⟨0,1⟩,locationShape location) := by
    have known := congrArg (fun entries => entries[0]?) rows
    simpa [homogeneous,Array.getElem?_eq_getElem valid,next] using known
  have entryEq : (after.locations.entries[0]'valid) = ⟨⟨0,1⟩,next⟩ :=
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
    (location : LocationTree) (offset : input.offset = 0) (length : input.len = 1)
    (initial : input.tree.locations = homogeneous 1 location) :
    (stage input).locations = homogeneous 1 (materialized location (index input) sharedState) := by
  change GeneralBorrowFreshMetadataChildShared.locations input = _
  exact full_locations input location offset length initial

/-- One actual shared newChild, including its actual SIFA result, forms raw
exposure Ready data. Only initial graph/allocator/range data are supplied.
This constructor result is not a proof of a complete retag or Rust history. -/
theorem append_ready (input : GeneralBorrowFreshMetadataChildShared.Input)
    (location : LocationTree) (offset : input.offset = 0) (length : input.len = 1)
    (initial : input.tree.locations = homogeneous 1 location)
    (parentless : input.parentNode.parent = none) :
    ∃ postLocation postRoot requestNode,
      (result input).locations = homogeneous 1 postLocation ∧
      Ready (result input) postLocation input.parent postRoot ⟨input.newTag,index input,requestNode⟩ ∧
      postLocation.exposedCache = location.exposedCache := by
  let after := result input
  have output := GeneralBorrowFreshMetadataChildShared.append input
  have atEnd := GeneralBorrowFreshMetadataChildShared.at_end input
  have installed := staged_locations input location offset length initial
  obtain ⟨postLocation,postLocations,postShape⟩ := shape_homogeneous (stage input) after
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

/-- The same actual constructor retains every previously Ready sibling. The
existential poststate is shared by the new leaf and the entire old family. -/
theorem append_ready_preserves (input : GeneralBorrowFreshMetadataChildShared.Input)
    (location : LocationTree) (offset : input.offset = 0) (length : input.len = 1)
    (initial : input.tree.locations = homogeneous 1 location)
    (parentless : input.parentNode.parent = none) :
    ∃ postLocation postRoot requestNode,
      (result input).locations = homogeneous 1 postLocation ∧
      Ready (result input) postLocation input.parent postRoot ⟨input.newTag,index input,requestNode⟩ ∧
      postLocation.exposedCache = location.exposedCache ∧
      ∀ (request : Request) (rootNode : TreeNode),
        Ready input.tree location input.parent rootNode request →
        ∃ nextNode, Ready (result input) postLocation input.parent postRoot
          ⟨request.tag,request.leaf,nextNode⟩ ∧ nextNode.tag = request.node.tag := by
  obtain ⟨postLocation,postRoot,newNode,postLocations,newReady,cacheEq⟩ :=
    append_ready input location offset length initial parentless
  refine ⟨postLocation,postRoot,newNode,postLocations,newReady,cacheEq,?_⟩
  intro request rootNode ready
  have atEnd := GeneralBorrowFreshMetadataChildShared.at_end input
  have notNew : request.leaf ≠ index input := by
    intro same
    have valid := GeneralBorrowNodeUpdate.lookup_valid input.tree.nodes request.leaf request.node ready.present
    rw [same,atEnd] at valid
    omega
  have staged : (stage input).nodeAt request.leaf = some request.node := by
    have original := GeneralBorrowFreshGraph.other_lookup input.tree (index input) input.parent
      request.leaf input.parentNode (sharedNode input.newTag input.parent) atEnd
      input.parentPresent (Ne.symm ready.different) notNew
    simpa only [GeneralBorrowFreshMetadataChildShared.stage,GeneralBorrowFreshMetadataChildAttach.staged,
      GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt] using original.trans ready.present
  obtain ⟨nextNode,present,tag,parent,_,_,exposed⟩ :=
    GeneralBorrowFreshMetadataChildSifa.node_fields (stage input) input.parent .Read
      request.leaf request.node staged
  rw [←tree_eq input] at present
  have differentTag : input.newTag ≠ request.tag := by
    intro same
    have tagged := ready.tagged
    rw [←same] at tagged
    simp only [BorrowTree.indexOfTag,UniKeyMap.get,
      GeneralBorrowTagMap.fresh_find _ _ input.fresh,Option.map_none] at tagged
    cases tagged
  have rows := congrArg (fun view => view.2.2.1) (shape input)
  change (result input).locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
    (stage input).locations.entries.map (fun segment => (segment.range,locationShape segment.data)) at rows
  rw [postLocations,staged_locations input location offset length initial] at rows
  have postShape : locationShape postLocation = locationShape (materialized location (index input) sharedState) := by
    simpa [homogeneous] using rows
  have frozen : ∃ state, postLocation.perms.get request.leaf = some state ∧ state.permission = .Frozen := by
    apply frozen_of_shape _ _ _ postShape
    obtain ⟨state,lookup,permission⟩ := ready.frozen
    exact ⟨state,(GeneralBorrowFreshLocation.get_other location.perms (index input) request.leaf sharedState notNew).trans lookup,permission⟩
  refine ⟨nextNode,?_,tag⟩
  exact ⟨(GeneralBorrowFreshMetadataChildShared.append input).oldLookup request.tag differentTag |>.trans ready.tagged,
    present,newReady.rootPresent,ready.different,parent.trans ready.parent,newReady.parentless,
    exposed.trans ready.unexposed,frozen⟩

end DuplicatePrefix.GeneralBorrowExposeReadFormation

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowExposeReadFormation." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual exposure formation dependency {dependency}"
