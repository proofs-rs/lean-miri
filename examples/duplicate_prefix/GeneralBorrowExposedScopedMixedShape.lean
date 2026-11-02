import duplicate_prefix.GeneralBorrowFreshMixedChild
import duplicate_prefix.GeneralBorrowExposedScopedOwnership
namespace DuplicatePrefix.GeneralBorrowExposedScopedMixedShape
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowView DuplicatePrefix.GeneralBorrowProjection
open DuplicatePrefix.GeneralBorrowFreshOwnership DuplicatePrefix.GeneralBorrowFreshReleaseMixed
open DuplicatePrefix.GeneralRangeMapOrigins
open DuplicatePrefix.GeneralBorrowNodeUpdate
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
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

private theorem required_shape (before after : LocationState) (same : stateShape after = stateShape before)
    (writable : Bool) (related : AccessRelatedness) (held : Bool)
    (owned : GeneralBorrowPermissions.Required before writable related held) :
    GeneralBorrowPermissions.Required after writable related held := by
  rcases before with ⟨oldPermission,oldAccessed,oldSifa⟩
  rcases after with ⟨permission,accessed,sifa⟩
  simp only [stateShape,Prod.mk.injEq] at same
  rcases same with ⟨rfl,rfl⟩
  cases writable <;> cases related <;> exact owned

theorem pointwise_shape (support : Nat → Prop) (before after : NormalTreeState) (same : normalShape after = normalShape before)
    (anchor : Nat) (writable : Nat → Bool)
    (owned : GeneralBorrowExposedScopedOwnership.Pointwise support before writable (GeneralBorrowAnchor.relation before anchor)) :
    GeneralBorrowExposedScopedOwnership.Pointwise support after writable (GeneralBorrowAnchor.relation after anchor) := by
  have topology : after.topology = before.topology := congrArg (fun row => row.1) same
  have protections : after.protectedNodes = before.protectedNodes := congrArg (fun row => row.2.2.2) same
  have locations : after.locationStates.map (Option.map stateShape) = before.locationStates.map (Option.map stateShape) :=
    congrArg (fun row => row.2.2.1) same
  have sizes : after.locationStates.size = before.locationStates.size := by
    have known := congrArg Array.size locations
    simpa only [Array.size_map] using known
  intro position supported valid
  obtain ⟨state,present,permitted⟩ := owned position supported (by rw [←sizes];exact valid)
  obtain ⟨next,actual,shape⟩ := state_transport before after same position state present
  refine ⟨next,actual,?_⟩
  have related : GeneralBorrowAnchor.relation after anchor position = GeneralBorrowAnchor.relation before anchor position := by
    unfold GeneralBorrowAnchor.relation
    rw [topology]
  rw [related,protections]
  exact required_shape state next shape (writable position) _ _ permitted

def Mixed (tree : BorrowTree) (protections : ProtectedTags) (anchor : UniIndex)
    (support : Nat → Prop) (writable : Nat → Bool) (location : LocationTree) : Prop :=
  GeneralBorrowExposedScopedOwnership.Pointwise support (source_normal_projection tree location protections) writable
    (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat)

theorem mixed_shape (before after : BorrowTree) (oldLocation newLocation : LocationTree) (protections : ProtectedTags)
    (profiles : normalShape (source_normal_projection after newLocation protections) =
      normalShape (source_normal_projection before oldLocation protections))
    (anchor : UniIndex) (support : Nat → Prop) (writable : Nat → Bool)
    (owned : Mixed before protections anchor support writable oldLocation) :
    Mixed after protections anchor support writable newLocation :=
  pointwise_shape support _ _ profiles anchor.toNat writable owned

theorem context_eq (tree : BorrowTree) (mapping : UniKeyMap BorTag)
    (locations : Miri.DataStructures.DedupRangeMap LocationTree) (location : LocationTree)
    (protections : ProtectedTags) (anchor : UniIndex) (support : Nat → Prop) (writable : Nat → Bool) :
    Mixed {tree with tagMapping := mapping,locations := locations} protections anchor support writable location =
      Mixed tree protections anchor support writable location := rfl

theorem map_eq (tree : BorrowTree) (locations : Miri.DataStructures.DedupRangeMap LocationTree)
    (location : LocationTree) (protections : ProtectedTags) (anchor : UniIndex) (support : Nat → Prop) (writable : Nat → Bool) :
    Mixed {tree with locations := locations} protections anchor support writable location =
      Mixed tree protections anchor support writable location := rfl
theorem shape_preserves (before after : BorrowTree) (same : treeShape after = treeShape before)
    (protections : ProtectedTags) (anchor : UniIndex) (support : Nat → Prop) (writable : Nat → Bool) (lower upper : UInt64)
    (owned : OwnedOn (Mixed before protections anchor support writable) lower upper before.locations) :
    OwnedOn (Mixed after protections anchor support writable) lower upper after.locations := by
  have nodes : after.nodes.data.map (Option.map nodeShape) = before.nodes.data.map (Option.map nodeShape) :=
    congrArg (fun row => row.2.1) same
  have ranges : after.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
      before.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) :=
    congrArg (fun row => row.2.2.1) same
  have sizes : after.locations.entries.size = before.locations.entries.size := by
    have known := congrArg Array.size ranges
    simpa only [Array.size_map] using known
  intro position valid positive beforeUpper afterLower
  have oldValid : position < before.locations.entries.size := by rw [←sizes];exact valid
  have entriesSame : (after.locations.entries[position]'valid).range =
        (before.locations.entries[position]'oldValid).range ∧
      locationShape (after.locations.entries[position]'valid).data =
        locationShape (before.locations.entries[position]'oldValid).data := by
    have known := congrArg (fun rows => rows[position]?) ranges
    simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,
      Array.getElem?_eq_getElem oldValid,Option.map_some] at known
    exact Prod.mk.inj (Option.some.inj known)
  rw [entriesSame.1] at beforeUpper afterLower
  have previous := owned position oldValid positive beforeUpper afterLower
  have profiles := GeneralBorrowFreshOwnership.projection_shape before after
    (before.locations.entries[position]'oldValid).data
    (after.locations.entries[position]'valid).data protections nodes entriesSame.2
  exact mixed_shape before after _ _ protections profiles anchor support writable previous

/-- The real ancestor SIFA update preserves every mixed writable label on
exactly the owned slice, regardless of its separately proved outcome. -/
theorem sifa_preserves (tree : BorrowTree) (start : UniIndex) (strongest : IdempotentForeignAccess)
    (protections : ProtectedTags) (anchor : UniIndex) (support : Nat → Prop) (writable : Nat → Bool) (lower upper : UInt64)
    (owned : OwnedOn (Mixed tree protections anchor support writable) lower upper tree.locations) :
    let next := (sourceUpdateSifa tree start strongest).1
    OwnedOn (Mixed next protections anchor support writable) lower upper next.locations := by
  exact shape_preserves tree _ (GeneralBorrowSifaView.preserves tree start strongest)
    protections anchor support writable lower upper owned
end DuplicatePrefix.GeneralBorrowExposedScopedMixedShape
