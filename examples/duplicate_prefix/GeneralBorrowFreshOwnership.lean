import duplicate_prefix.GeneralBorrowFreshEntries
import duplicate_prefix.GeneralBorrowSifaView
import duplicate_prefix.GeneralBorrowRange
namespace DuplicatePrefix.GeneralBorrowFreshOwnership
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowView
open DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Only the permission, accessed bit, topology and protector membership enter
AnchorOwned. SIFA caches are intentionally absent from this data projection. -/
def normalShape (tree : NormalTreeState) :=
  (tree.topology,tree.defaultStates.map stateShape,tree.locationStates.map (Option.map stateShape),tree.protectedNodes)

def topologyFrom (nodes : Array (Option NodeShape)) : TraversalTree :=
  ⟨nodes.map fun row => match row with
    | none => ⟨none,[]⟩
    | some node => ⟨node.2.1.map UniIndex.toNat,node.2.2.1.toList.map UniIndex.toNat⟩⟩

def defaultsFrom (nodes : Array (Option NodeShape)) : Array StateShape :=
  nodes.map fun row => match row with
    | none => (.Disabled,false)
    | some node => (node.2.2.2,false)

def locationsFrom (nodes : Array (Option NodeShape)) (states : Array (Option StateShape)) : Array (Option StateShape) :=
  nodes.mapIdx fun position _ => match UniIndex.ofNat? position with
    | none => none
    | some index => states[index.toNat]?.getD none

def protectionsFrom (nodes : Array (Option NodeShape)) (protections : ProtectedTags) : List Nat :=
  (⟨nodes⟩ : UniValMap NodeShape).entries.toList.filterMap fun row =>
    if protections.contains row.2.1 then some row.1.toNat else none

private theorem topology_factor (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection tree location protections).topology = topologyFrom (tree.nodes.data.map (Option.map nodeShape)) := by
  unfold_general_projection
  unfold_general_topology
  unfold topologyFrom
  apply congrArg TraversalTree.mk
  simp only [Array.map_map,Function.comp_def]
  apply Array.map_congr_left
  intro row member
  cases row <;> rfl

private theorem defaults_factor (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection tree location protections).defaultStates.map stateShape = defaultsFrom (tree.nodes.data.map (Option.map nodeShape)) := by
  unfold_general_projection
  unfold defaultsFrom
  simp only [Array.map_map,Function.comp_def]
  apply Array.map_congr_left
  intro row member
  cases row <;> rfl

private theorem get_shape (location : LocationTree) (index : UniIndex) :
    (location.perms.get index).map stateShape = (locationShape location)[index.toNat]?.getD none := by
  unfold UniValMap.get locationShape
  simp only [Array.getElem?_map]
  cases location.perms.data[index.toNat]? <;> rfl

private theorem locations_factor (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection tree location protections).locationStates.map (Option.map stateShape) =
      locationsFrom (tree.nodes.data.map (Option.map nodeShape)) (locationShape location) := by
  unfold_general_projection
  unfold locationsFrom
  apply Array.ext
  · simp only [Array.size_map,Array.size_mapIdx]
  · intro position left right
    simp only [Array.getElem_map,Array.getElem_mapIdx]
    cases UniIndex.ofNat? position with
    | none => rfl
    | some index => exact get_shape location index

private theorem protections_factor (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection tree location protections).protectedNodes =
      protectionsFrom (tree.nodes.data.map (Option.map nodeShape)) protections := by
  unfold_general_projection
  unfold protectionsFrom
  rw [GeneralBorrowFreshEntries.entries_map nodeShape tree.nodes]
  simp only [Array.toList_map,List.filterMap_map,Function.comp_def,nodeShape]

/-- The real normal projection depends on exactly the retained data shapes. -/
theorem projection_shape (before after : BorrowTree) (oldLocation newLocation : LocationTree)
    (protections : ProtectedTags)
    (nodes : after.nodes.data.map (Option.map nodeShape) = before.nodes.data.map (Option.map nodeShape))
    (locations : locationShape newLocation = locationShape oldLocation) :
    normalShape (source_normal_projection after newLocation protections) =
      normalShape (source_normal_projection before oldLocation protections) := by
  unfold normalShape
  rw [topology_factor after newLocation protections,defaults_factor after newLocation protections,
    locations_factor after newLocation protections,protections_factor after newLocation protections,
    topology_factor before oldLocation protections,defaults_factor before oldLocation protections,
    locations_factor before oldLocation protections,protections_factor before oldLocation protections,nodes,locations]

private theorem state_factor (tree : NormalTreeState) (position : Nat) :
    (tree.stateAt position).map stateShape =
      match (tree.locationStates.map (Option.map stateShape))[position]? with
      | none => none
      | some (some shape) => some shape
      | some none => (tree.defaultStates.map stateShape)[position]? := by
  unfold NormalTreeState.stateAt
  simp only [Array.getElem?_map]
  cases tree.locationStates[position]? with
  | none => rfl
  | some row => cases row <;> rfl

private theorem state_transport (before after : NormalTreeState) (same : normalShape after = normalShape before)
    (position : Nat) (state : LocationState) (present : before.stateAt position = some state) :
    ∃ next, after.stateAt position = some next ∧ stateShape next = stateShape state := by
  have defaults : after.defaultStates.map stateShape = before.defaultStates.map stateShape :=
    congrArg (fun row => row.2.1) same
  have locations : after.locationStates.map (Option.map stateShape) = before.locationStates.map (Option.map stateShape) :=
    congrArg (fun row => row.2.2.1) same
  have lookup : (after.stateAt position).map stateShape = some (stateShape state) := by
    rw [state_factor,locations,defaults]
    rw [←state_factor,present]
    rfl
  cases actual : after.stateAt position with
  | none => rw [actual] at lookup; cases lookup
  | some next => rw [actual] at lookup; exact ⟨next,rfl,Option.some.inj lookup⟩

private theorem access_owned_shape (before after : LocationState) (same : stateShape after = stateShape before)
    (kind : AccessKind) (related : AccessRelatedness) (held : Bool)
    (owned : GeneralBorrowPermissions.AccessOwned before kind related held) :
    GeneralBorrowPermissions.AccessOwned after kind related held := by
  rcases before with ⟨oldPermission,oldAccessed,oldSifa⟩
  rcases after with ⟨permission,accessed,sifa⟩
  simp only [stateShape,Prod.mk.injEq] at same
  rcases same with ⟨rfl,rfl⟩
  cases kind <;> cases related <;> exact owned

/-- Ownership is insensitive to SIFA-only changes. This transports a data
invariant; it does not classify a failed SIFA operation as safe completion. -/
theorem anchor_owned (before after : NormalTreeState) (same : normalShape after = normalShape before)
    (anchor : Nat) (kind : AccessKind) (owned : GeneralBorrowAnchor.AnchorOwned before anchor kind) :
    GeneralBorrowAnchor.AnchorOwned after anchor kind := by
  have topology : after.topology = before.topology := congrArg (fun row => row.1) same
  have defaults : after.defaultStates.map stateShape = before.defaultStates.map stateShape :=
    congrArg (fun row => row.2.1) same
  have locations : after.locationStates.map (Option.map stateShape) = before.locationStates.map (Option.map stateShape) :=
    congrArg (fun row => row.2.2.1) same
  have protections : after.protectedNodes = before.protectedNodes := congrArg (fun row => row.2.2.2) same
  have defaultSizes := congrArg Array.size defaults
  have locationSizes := congrArg Array.size locations
  simp only [Array.size_map] at defaultSizes locationSizes
  refine ⟨by rw [topology];exact owned.anchorValid,?_,?_,?_⟩
  · rw [locationSizes,topology]
    exact owned.locationsAligned
  · rw [defaultSizes,topology]
    exact owned.defaultsAligned
  · intro position valid
    obtain ⟨state,present,permitted⟩ := owned.permissions position (by rw [←topology];exact valid)
    obtain ⟨next,actual,shape⟩ := state_transport before after same position state present
    refine ⟨next,actual,?_⟩
    have related : GeneralBorrowAnchor.relation after anchor position = GeneralBorrowAnchor.relation before anchor position := by
      unfold GeneralBorrowAnchor.relation
      rw [topology]
    rw [related,protections]
    exact access_owned_shape state next shape kind _ _ permitted

/-- The real ancestor-SIFA update preserves the full per-location ownership
contract for an arbitrary range partition. This is data preservation on either
outcome; successful newChild execution must still discharge its outcome. -/
theorem sifa_preserves (tree : BorrowTree) (start : UniIndex) (strongest : IdempotentForeignAccess)
    (protections : ProtectedTags) (anchor : UniIndex) (kind : AccessKind)
    (owned : Every (GeneralBorrowRange.LocationOwned tree protections anchor kind) tree.locations) :
    let next := (sourceUpdateSifa tree start strongest).1
    Every (GeneralBorrowRange.LocationOwned next protections anchor kind) next.locations := by
  dsimp only
  generalize result : (sourceUpdateSifa tree start strongest).1 = next
  have preserved := GeneralBorrowSifaView.preserves tree start strongest
  rw [result] at preserved
  have nodes : next.nodes.data.map (Option.map nodeShape) = tree.nodes.data.map (Option.map nodeShape) :=
    congrArg (fun row => row.2.1) preserved
  have ranges : next.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
      tree.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) :=
    congrArg (fun row => row.2.2.1) preserved
  have sizes : next.locations.entries.size = tree.locations.entries.size := by
    have known := congrArg Array.size ranges
    simpa only [Array.size_map] using known
  intro position valid
  have validOld : position < tree.locations.entries.size := by rw [←sizes];exact valid
  have entriesSame : some ((next.locations.entries[position]'valid).range,
        locationShape (next.locations.entries[position]'valid).data) =
      some ((tree.locations.entries[position]'validOld).range,
        locationShape (tree.locations.entries[position]'validOld).data) := by
    have known := congrArg (fun rows => rows[position]?) ranges
    simpa only [Array.getElem?_map,Array.getElem?_eq_getElem valid,
      Array.getElem?_eq_getElem validOld,Option.map_some] using known
  have locations := congrArg Prod.snd (Option.some.inj entriesSame)
  have profiles := projection_shape tree next (tree.locations.entries[position]'validOld).data
    (next.locations.entries[position]'valid).data protections nodes locations
  have previous := owned position validOld
  rcases previous with ⟨forest,owner⟩
  refine ⟨?_,anchor_owned _ _ profiles anchor.toNat kind owner⟩
  have topology : (source_normal_projection next (next.locations.entries[position]'valid).data protections).topology =
      (source_normal_projection tree (tree.locations.entries[position]'validOld).data protections).topology :=
    congrArg (fun row => row.1) profiles
  rw [topology]
  exact forest

end DuplicatePrefix.GeneralBorrowFreshOwnership
#print axioms DuplicatePrefix.GeneralBorrowFreshOwnership.sifa_preserves
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshOwnership." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved SIFA ownership transport dependency {dependency}"
