import duplicate_prefix.GeneralBorrowFreshOwnership
import duplicate_prefix.DuplicatePrefixScalarAuthorization
import duplicate_prefix.GeneralBorrowFreshAnchor
namespace DuplicatePrefix.DuplicatePrefixConstructorNormalShape
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowView GeneralBorrowFreshOwnership
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

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

/-- Exact normal scalar compatibility depends on permission/accessed/protector
state, never on the SIFA cache that constructors weaken. -/
theorem compatible_shape (before after : LocationState) (same : stateShape after = stateShape before)
    (kind : AccessKind) (related : AccessRelatedness) (held : Bool)
    (compatible : DuplicatePrefixScalarAuthorization.Compatible before kind related held) :
    DuplicatePrefixScalarAuthorization.Compatible after kind related held := by
  rcases before with ⟨oldPermission,oldAccessed,oldSifa⟩
  rcases after with ⟨permission,accessed,sifa⟩
  simp only [stateShape,Prod.mk.injEq] at same
  rcases same with ⟨rfl,rfl⟩
  cases kind <;> cases related <;> exact compatible

/-- Per-kind normal permissions transport through real SIFA-preserved normal
shape. Support is arbitrary; no exact ownership profile is required. -/
theorem permissions (before after : NormalTreeState) (same : normalShape after = normalShape before)
    (anchor : Nat) (kind : AccessKind) (support : Nat → Prop)
    (owned : ∀ index, support index → index < before.topology.nodes.size → ∃ state,
      before.stateAt index = some state ∧ DuplicatePrefixScalarAuthorization.Compatible state kind
        (GeneralBorrowAnchor.relation before anchor index) (before.protectedNodes.contains index)) :
    ∀ index, support index → index < after.topology.nodes.size → ∃ state,
      after.stateAt index = some state ∧ DuplicatePrefixScalarAuthorization.Compatible state kind
        (GeneralBorrowAnchor.relation after anchor index) (after.protectedNodes.contains index) := by
  have topology : after.topology = before.topology := congrArg (fun row => row.1) same
  have protections : after.protectedNodes = before.protectedNodes := congrArg (fun row => row.2.2.2) same
  intro index included valid
  obtain ⟨state,present,compatible⟩ := owned index included (by rw [←topology];exact valid)
  obtain ⟨next,actual,shape⟩ := state_transport before after same index state present
  refine ⟨next,actual,?_⟩
  have related : GeneralBorrowAnchor.relation after anchor index = GeneralBorrowAnchor.relation before anchor index := by
    unfold GeneralBorrowAnchor.relation
    rw [topology]
  rw [related,protections]
  exact compatible_shape state next shape kind _ _ compatible

/-- A new shared source has the exact local Read capability for either
protector status. It is an intermediate helper capability, not a Both Row. -/
theorem shared_local_read (held : Bool) :
    DuplicatePrefixScalarAuthorization.Compatible GeneralBorrowFreshAnchor.sharedState .Read .LocalAccess held := by
  cases held <;> simp [DuplicatePrefixScalarAuthorization.Compatible,GeneralBorrowProtectedReadCompatible.Compatible,GeneralBorrowFreshAnchor.sharedState,LocationState.possible]

/-- For an original mutable source, the new shared child can be included as
an unprotected foreign descendant in both exact scalar tables. -/
theorem shared_foreign_both (kind : AccessKind) :
    DuplicatePrefixScalarAuthorization.Compatible GeneralBorrowFreshAnchor.sharedState kind .ForeignAccess false := by
  cases kind <;> simp [DuplicatePrefixScalarAuthorization.Compatible,GeneralBorrowProtectedReadCompatible.Compatible,GeneralBorrowExposedConditionalWritePermissions.Compatible,GeneralBorrowFreshAnchor.sharedState,GeneralBorrowFreshAnchor.sharedNode,TreeNode.defaultLocationState,LocationState.possible,Permission.isUnique]

/-- The lazy shared default is also both-kind foreign-compatible when the
fresh shared tag is not in the current protector table. -/
theorem shared_default_foreign_both (tag : BorTag) (parent : UniIndex) (kind : AccessKind) :
    DuplicatePrefixScalarAuthorization.Compatible (GeneralBorrowFreshAnchor.sharedNode tag parent).defaultLocationState kind .ForeignAccess false := by
  cases kind <;> simp [DuplicatePrefixScalarAuthorization.Compatible,GeneralBorrowProtectedReadCompatible.Compatible,GeneralBorrowExposedConditionalWritePermissions.Compatible,GeneralBorrowFreshAnchor.sharedState,GeneralBorrowFreshAnchor.sharedNode,TreeNode.defaultLocationState,LocationState.possible,Permission.isUnique]

end DuplicatePrefix.DuplicatePrefixConstructorNormalShape
