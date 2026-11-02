import duplicate_prefix.GeneralBorrowTwoRootUniqueParentRead
import duplicate_prefix.GeneralBorrowReadUnique
import duplicate_prefix.GeneralBorrowSifaUniqueFrame
namespace DuplicatePrefix.GeneralBorrowSharedStepClosure
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowExposeReadFold
open DuplicatePrefix.GeneralBorrowFreshAnchor DuplicatePrefix.GeneralBorrowFreshMaterialization
open DuplicatePrefix.GeneralBorrowFreshGraph DuplicatePrefix.GeneralBorrowView DuplicatePrefix.RangeMapNonempty
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

open Lean Elab Term in
elab "checked_staged_locations" : term => do
  let found := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".GeneralBorrowExposeReadFormation.staged_locations" then some name else none
  match found with
  | [name] => return mkConst name
  | _ => throwError "expected checked actual shared-stage range theorem"

private theorem map_get {α β : Type} (f : α → β) (nodes : UniValMap α) (query : UniIndex) :
    (⟨nodes.data.map (Option.map f)⟩ : UniValMap β).get query = (nodes.get query).map f := by
  unfold UniValMap.get
  simp only [Array.getElem?_map]
  cases row : nodes.data[query.toNat]? with
  | none => rfl
  | some entry => cases entry <;> rfl

private theorem unique_of_shape (before after : LocationTree) (query : UniIndex)
    (shape : locationShape after = locationShape before)
    (unique : ∃ state, before.perms.get query = some state ∧ state.permission = .Unique) :
    ∃ state, after.perms.get query = some state ∧ state.permission = .Unique := by
  obtain ⟨old,stored,permission⟩ := unique
  have lookups := congrArg (fun entries => (⟨entries⟩ : UniValMap StateShape).get query) shape
  dsimp only [locationShape] at lookups
  rw [map_get,map_get,stored] at lookups
  cases found : after.perms.get query with
  | none => simp [found] at lookups
  | some state =>
    have equal : stateShape state = stateShape old := by simpa [found] using lookups
    exact ⟨state,rfl,(congrArg Prod.fst equal).trans permission⟩

/-- A single real append retains the raw foreign leaf witness and selected
parent's stored Unique permission in the same poststate as its Ready family.
The actual roots and parent tag are retained, without poststate hypotheses. -/
theorem append_closed (input : GeneralBorrowFreshMetadataChildShared.Input) (location : LocationTree)
    (offset : input.offset = 0) (length : input.len = 1)
    (initial : input.tree.locations = homogeneous 1 location) (parentless : input.parentNode.parent = none)
    (foreignRoot : UniIndex) (foreignNode : TreeNode) (different : input.parent ≠ foreignRoot)
    (foreign : GeneralBorrowWildcardLeaf.Data input.tree location foreignRoot foreignNode input.parentNode.tag)
    (unique : ∃ state, location.perms.get input.parent = some state ∧ state.permission = .Unique) :
    ∃ postLocation postRoot requestNode postForeign,
      (result input).locations = homogeneous 1 postLocation ∧
      Ready (result input) postLocation input.parent postRoot ⟨input.newTag,index input,requestNode⟩ ∧
      postLocation.exposedCache = location.exposedCache ∧
      (∀ (request : Request) (rootNode : TreeNode), Ready input.tree location input.parent rootNode request →
        ∃ nextNode, Ready (result input) postLocation input.parent postRoot ⟨request.tag,request.leaf,nextNode⟩ ∧ nextNode.tag = request.node.tag) ∧
      GeneralBorrowWildcardLeaf.Data (result input) postLocation foreignRoot postForeign postRoot.tag ∧
      (∃ state, postLocation.perms.get input.parent = some state ∧ state.permission = .Unique) ∧
      (result input).roots = input.tree.roots ∧ postRoot.tag = input.parentNode.tag := by
  obtain ⟨postLocation,postRoot,newNode,locations,newReady,cache,preserved⟩ :=
    GeneralBorrowExposeReadFormation.append_ready_preserves input location offset length initial parentless
  have installed := checked_staged_locations input location offset length initial
  have atEnd := GeneralBorrowFreshMetadataChildShared.at_end input
  have parentNotNew := GeneralBorrowFreshNode.parent_not_fresh input.tree.nodes (index input) input.parent input.parentNode atEnd input.parentPresent
  have foreignNotNew := GeneralBorrowFreshNode.parent_not_fresh input.tree.nodes (index input) foreignRoot foreignNode atEnd foreign.present
  have foreignStage : (stage input).nodeAt foreignRoot = some foreignNode := by
    have lookup := GeneralBorrowFreshGraph.other_lookup input.tree (index input) input.parent foreignRoot input.parentNode
      (sharedNode input.newTag input.parent) atEnd input.parentPresent (Ne.symm different) foreignNotNew
    simpa only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt] using lookup.trans foreign.present
  obtain ⟨postForeign,foreignPresent,foreignTag,_,foreignChildren,_,foreignExposed⟩ :=
    GeneralBorrowFreshMetadataChildSifa.node_fields (stage input) input.parent .Read foreignRoot foreignNode foreignStage
  rw [←tree_eq input] at foreignPresent
  have rootStage : (stage input).nodeAt input.parent = some (updatedParent input.parentNode (index input)) := by
    simpa only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt] using
      GeneralBorrowFreshGraph.parent_lookup input.tree (index input) input.parent input.parentNode
        (sharedNode input.newTag input.parent) atEnd input.parentPresent
  obtain ⟨actualRoot,rootPresent,rootTag,_,_,_⟩ := GeneralBorrowFreshMetadata.node_fields
    (stage input) (result input) (shape input) input.parent (updatedParent input.parentNode (index input)) rootStage
  have rootEqual : actualRoot = postRoot := Option.some.inj (rootPresent.symm.trans newReady.rootPresent)
  have tag : postRoot.tag = input.parentNode.tag := by rw [←rootEqual];exact rootTag
  have stageUnique : GeneralBorrowSifaUniqueFrame.UniqueAt (stage input) foreignRoot := by
    rw [GeneralBorrowSifaUniqueFrame.UniqueAt,installed]
    intro position valid
    have zero : position = 0 := by simpa only [homogeneous,Array.size_singleton] using Nat.lt_one_iff.mp valid
    subst position
    simpa only [homogeneous,Array.getElem_singleton,materialized,GeneralBorrowFreshLocation.get_other _ (index input) foreignRoot sharedState foreignNotNew] using foreign.writable
  have afterUnique := GeneralBorrowSifaUniqueFrame.sifa_unique (stage input) input.parent .Read foreignRoot stageUnique
  rw [←tree_eq input] at afterUnique
  have foreignStored : postLocation.perms.get foreignRoot = some GeneralBorrowWildcardLeaf.unique := by
    rw [GeneralBorrowSifaUniqueFrame.UniqueAt,locations] at afterUnique
    exact afterUnique 0 (by change 0<1;decide)
  have rows := congrArg (fun view => view.2.2.1) (shape input)
  change (result input).locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
    (stage input).locations.entries.map (fun segment => (segment.range,locationShape segment.data)) at rows
  rw [locations,installed] at rows
  have postShape : locationShape postLocation = locationShape (materialized location (index input) sharedState) := by simpa [homogeneous] using rows
  have rootUnique : ∃ state, postLocation.perms.get input.parent = some state ∧ state.permission = .Unique := by
    apply unique_of_shape _ _ _ postShape
    obtain ⟨state,stored,permission⟩ := unique
    exact ⟨state,(GeneralBorrowFreshLocation.get_other location.perms (index input) input.parent sharedState parentNotNew).trans stored,permission⟩
  refine ⟨postLocation,postRoot,newNode,postForeign,locations,newReady,cache,preserved,?_,rootUnique,
    (GeneralBorrowFreshMetadataChildShared.append input).roots,tag⟩
  exact ⟨foreignPresent,foreignChildren.trans foreign.leaf,foreignExposed.trans foreign.exposed,foreignStored,
    by rw [cache];exact foreign.cache,by rw [tag,foreignTag];exact foreign.boundedTag⟩
end DuplicatePrefix.GeneralBorrowSharedStepClosure
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowSharedStepClosure." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved shared generator closure dependency {dependency}"
