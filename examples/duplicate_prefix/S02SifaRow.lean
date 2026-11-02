import duplicate_prefix.S02SifaCallbacks
import duplicate_prefix.GeneralBorrowFreshOwnership
import duplicate_prefix.DuplicatePrefixBorrowAuthorization

namespace DuplicatePrefix.S02SifaRow
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowSifa GeneralBorrowProjection GeneralBorrowView GeneralBorrowFreshOwnership DuplicatePrefixBorrowAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

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
  have defaults := congrArg (fun row => row.2.1) same
  have locations := congrArg (fun row => row.2.2.1) same
  dsimp only [normalShape] at defaults locations
  have lookup : (after.stateAt position).map stateShape = some (stateShape state) := by
    rw [state_factor,locations,defaults,←state_factor,present]
    rfl
  cases actual : after.stateAt position with
  | none => rw [actual] at lookup; cases lookup
  | some next => rw [actual] at lookup;exact ⟨next,rfl,Option.some.inj lookup⟩

private theorem compatible_shape (before after : LocationState) (same : stateShape after = stateShape before)
    (kind : AccessKind) (related : AccessRelatedness) (held : Bool)
    (old : DuplicatePrefixScalarAuthorization.Compatible before kind related held) :
    DuplicatePrefixScalarAuthorization.Compatible after kind related held := by
  rcases before with ⟨oldPermission,oldAccessed,oldSifa⟩
  rcases after with ⟨permission,accessed,sifa⟩
  simp only [stateShape,Prod.mk.injEq] at same
  rcases same with ⟨rfl,rfl⟩
  cases kind <;> cases related <;> exact old

/-- The normal source capability depends only on topology, permission,
accessed state and protector membership, all preserved by SIFA. -/
theorem normal (before after : BorrowTree) (oldLocation newLocation : LocationTree)
    (protections : ProtectedTags) (source : UniIndex)
    (nodes : after.nodes.data.map (Option.map nodeShape) = before.nodes.data.map (Option.map nodeShape))
    (locations : locationShape newLocation = locationShape oldLocation)
    (old : Normal before oldLocation protections source) :
    Nonempty (Normal after newLocation protections source) := by
  have projected := projection_shape before after oldLocation newLocation protections nodes locations
  have topology := congrArg (fun row => row.1) projected
  have topologyDefault := congrArg (fun row => row.1)
    (projection_shape before after default default protections nodes rfl)
  have held := congrArg (fun row => row.2.2.2) projected
  dsimp only [normalShape] at topology topologyDefault held
  let component : GeneralBorrowExposedScopedNormal.Component
      (source_normal_projection after default protections).topology source.toNat := {
    support := old.component.support
    anchor := old.component.anchor
    parents := by rw [topologyDefault];exact old.component.parents
    children := by rw [topologyDefault];exact old.component.children }
  refine ⟨⟨component,?_⟩⟩
  intro kind index included valid
  have oldIncluded : old.component.support index := included
  have sizes : after.nodes.data.size = before.nodes.data.size := by
    have := congrArg Array.size nodes
    simpa only [Array.size_map] using this
  obtain ⟨state,present,compatible⟩ := old.permissions kind index oldIncluded (by omega)
  obtain ⟨next,nextPresent,same⟩ := state_transport _ _ projected index state present
  refine ⟨next,nextPresent,?_⟩
  have relation : GeneralBorrowAnchor.relation (source_normal_projection after newLocation protections) source.toNat index =
      GeneralBorrowAnchor.relation (source_normal_projection before oldLocation protections) source.toNat index := by
    unfold GeneralBorrowAnchor.relation
    rw [topology]
  rw [relation,held]
  exact compatible_shape state next same kind _ _ compatible

/-- Once the complete callback family is transported, every other Row field
follows from the exact metadata shape. No source/constructor-parent equality
is required. -/
theorem row (before after : BorrowTree) (oldLocation newLocation : LocationTree)
    (protections : ProtectedTags) (source selected : Option UniIndex) (maximum : Option BorTag)
    (shape : treeShape after = treeShape before)
    (locations : locationShape newLocation = locationShape oldLocation)
    (old : Row before oldLocation protections source selected maximum)
    (callbacks : S02SifaCallbacks.Callbacks after protections selected maximum newLocation) :
    Nonempty (Row after newLocation protections source selected maximum) := by
  have nodes := GeneralBorrowFreshMetadata.node_array before after shape
  have topology := congrArg (fun row => row.1)
    (projection_shape before after oldLocation newLocation protections nodes locations)
  dsimp only [normalShape] at topology
  refine ⟨{wildcard := old.wildcard,rootPath := ?_,rootPresent := ?_,cutoff := ?_,normal := ?_,callbacks := callbacks}⟩
  · intro anchor same
    rw [topology]
    exact old.rootPath anchor same
  · intro root same
    obtain ⟨node,present⟩ := old.rootPresent root same
    obtain ⟨next,found,_⟩ := GeneralBorrowFreshMetadata.node_fields before after shape root node present
    exact ⟨next,found⟩
  · rw [old.cutoff]
    cases selected with
    | none => rfl
    | some root =>
      obtain ⟨node,present⟩ := old.rootPresent root rfl
      obtain ⟨next,found,tag,_⟩ := GeneralBorrowFreshMetadata.node_fields before after shape root node present
      change after.nodeAt root = some next at found
      simp only [Option.bind_some,present,found,Option.map_some,tag]
  · intro anchor same
    obtain ⟨owned⟩ := old.normal anchor same
    exact normal before after oldLocation newLocation protections anchor nodes locations owned

/-- Actual constructor SIFA preserves the full destination Row family on its
physical byte window, regardless of source/selected-root coincidence. -/
theorem owned (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (start : UniIndex) (protections : ProtectedTags) (source selected : Option UniIndex)
    (maximum : Option BorTag) (lower upper : UInt64)
    (profile : GeneralRangeMapState.Every (fun location => GeneralBorrowLocationSifaConsistency.Profile tree location protections) tree.locations)
    (initial : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (Row tree location protections source selected maximum)) lower upper tree.locations) :
    let after := (sourceUpdateSifa tree start .Read).1
    GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (Row after location protections source selected maximum)) lower upper after.locations := by
  let after := (sourceUpdateSifa tree start .Read).1
  have callbacksBefore : GeneralRangeMapOrigins.OwnedOn (S02SifaCallbacks.Callbacks tree protections selected maximum)
      lower upper tree.locations := by
    intro position valid positive start stop
    obtain ⟨old⟩ := initial position valid positive start stop
    exact old.callbacks
  have callbacksAfter := S02SifaCallbacks.owned tree depth start protections selected maximum lower upper profile callbacksBefore
  have shape := GeneralBorrowSifaView.preserves tree start .Read
  have ranges := congrArg (fun value => value.2.2.1) shape
  change after.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
    tree.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) at ranges
  have sizes := congrArg Array.size ranges
  simp only [Array.size_map] at sizes
  change GeneralRangeMapOrigins.OwnedOn
    (fun location => Nonempty (Row after location protections source selected maximum)) lower upper after.locations
  intro position valid positive start stop
  have previous : position < tree.locations.entries.size := by omega
  have known := congrArg (fun rows => rows[position]?) ranges
  simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,
    Array.getElem?_eq_getElem previous,Option.map_some] at known
  have rangeEq := congrArg Prod.fst (Option.some.inj known)
  have locationEq := congrArg Prod.snd (Option.some.inj known)
  dsimp only [Prod.fst,Prod.snd] at rangeEq locationEq
  have oldStart := start
  have oldStop := stop
  rw [rangeEq] at oldStart oldStop
  obtain ⟨old⟩ := initial position previous positive oldStart oldStop
  exact row tree after _ _ protections source selected maximum shape locationEq old
    (callbacksAfter position valid positive start stop)

end DuplicatePrefix.S02SifaRow
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02SifaRow.normal,``DuplicatePrefix.S02SifaRow.row,``DuplicatePrefix.S02SifaRow.owned] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
