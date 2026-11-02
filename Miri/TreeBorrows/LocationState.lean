import Miri.TreeBorrows.Permissions

/-!
The state and per-location update layer from pinned Miri
`tree_borrows/tree.rs`. This is below the allocation-wide range map and tree
visitor: it keeps the initialization/accessed bit, permission, SIFA cache,
and the exact permission/protector error ordering for one tree node at one
location.
-/

namespace Miri.TreeBorrows

namespace Diagnostics

/-- Transition errors emitted by the per-location layer. `ProtectedDealloc`
belongs to the later tree-wide deallocation check. -/
inductive TransitionError where
  | ChildAccessForbidden (permission : Permission)
  | ProtectedDisabled (permission : Permission)
  | ProtectedDealloc
  deriving DecidableEq, Repr, Inhabited

end Diagnostics

namespace Tree

/-- The two continuation results used by Miri's tree visitor. -/
inductive ContinueTraversal where
  | Recurse
  | SkipSelfAndChildren
  deriving DecidableEq, Repr, Inhabited

/-- Per-node state at one allocation location. A false `accessed` bit stores
the future initial permission for a location that has not yet been reached by
a child pointer. -/
structure LocationState where
  permission : Permission
  accessed : Bool
  idempotentForeignAccess : IdempotentForeignAccess
  deriving DecidableEq, Repr

namespace LocationState

/-- Construction failures corresponding to the source `assert!`s. -/
inductive ConstructionResult where
  | Constructed (state : LocationState)
  | PermissionNotInitialOrDisabled
  | UniquePermissionNotAccessed
  deriving DecidableEq, Repr

/-- Source `new_non_accessed`, with its assertions retained as explicit
outcomes. -/
def newNonAccessed (permission : Permission)
    (sifa : IdempotentForeignAccess) : ConstructionResult :=
  if permission.isInitial || permission.isDisabled then
    if permission.isUnique then .UniquePermissionNotAccessed
    else .Constructed ⟨permission, false, sifa⟩
  else .PermissionNotInitialOrDisabled

/-- Source `new_accessed` has no validity assertions. -/
def newAccessed (permission : Permission) (sifa : IdempotentForeignAccess) :
    LocationState := ⟨permission, true, sifa⟩

/-- A lazy `Unique` state is unreachable; every other permission is possible
regardless of whether its location has been accessed. -/
def possible (state : LocationState) : Bool :=
  state.accessed || !state.permission.isUnique

/-- Check whether any child pointer has accessed this location. -/
def isAccessed (state : LocationState) : Bool := state.accessed

/-- Current permission or future initial permission. -/
def currentPermission (state : LocationState) : Permission := state.permission

/-- Result of the tree traversal's per-node skip predicate. -/
def skipIfKnownNoop (state : LocationState) (accessKind : AccessKind)
    (relatedness : AccessRelatedness) : ContinueTraversal :=
  if relatedness.isForeign then
    let happeningNow := IdempotentForeignAccess.fromForeign accessKind
    let sifaSaysNoop :=
      match IdempotentForeignAccess.canSkipForeignAccess state.idempotentForeignAccess happeningNow with
      | .Decision canSkip => canSkip
      | .DebugAssertion => false
    if sifaSaysNoop || state.permission.isDisabled ||
        (state.permission.isFrozen && accessKind == .Read) then
      .SkipSelfAndChildren
    else .Recurse
  else .Recurse

/-- SIFA update with the source debug-assert precondition represented as a
separate result. -/
inductive RecordAccessResult where
  | Recorded (state : LocationState)
  | DebugAssertion
  deriving DecidableEq, Repr

/-- Source `record_new_access`; callers must only record accesses whose
skip-check result is `Recurse`. -/
def recordNewAccess (state : LocationState) (accessKind : AccessKind)
    (relatedness : AccessRelatedness) : RecordAccessResult :=
  if state.skipIfKnownNoop accessKind relatedness == .Recurse then
    .Recorded { state with idempotentForeignAccess := (
      IdempotentForeignAccess.recordNew state.idempotentForeignAccess
        (IdempotentForeignAccess.fromAccessAndRelatedness accessKind relatedness)) }
  else .DebugAssertion

/-- Result of applying one access to one location, including the resulting
state on source `Err` results. Miri mutates the state before returning a
`ProtectedDisabled` error. -/
inductive AccessResult where
  | Success (state : LocationState) (transition : PermTransition)
  | Error (state : LocationState) (error : Diagnostics.TransitionError)
  | PermissionInvariantFailure (state : LocationState)
  | TransitionApplicationInvariantFailure (state : LocationState)
  | PossibleInvariantFailure (state : LocationState)
  deriving DecidableEq, Repr

/-- The location state after a call, including state retained on source errors. -/
def AccessResult.resultingState : AccessResult → LocationState
  | .Success state _ | .Error state _ | .PermissionInvariantFailure state
  | .TransitionApplicationInvariantFailure state | .PossibleInvariantFailure state => state

/-- Apply `LocationState::perform_access` in source order.

Permission failure leaves the old location untouched. Otherwise the access
bit and permission are updated before the protector check; thus a protected
transition to `Disabled` is an error only if the location is now accessed. -/
def performAccess (state : LocationState) (accessKind : AccessKind)
    (relatedness : AccessRelatedness) (isProtected : Bool) : AccessResult :=
  match performAccessTransition accessKind relatedness state.permission isProtected with
  | .UndefinedBehavior =>
      .Error state (.ChildAccessForbidden state.permission)
  | .ImpossibleProtectedReservedIM =>
      .PermissionInvariantFailure state
  | .Transition transition =>
      match transition.applied state.permission with
      | none => .TransitionApplicationInvariantFailure state
      | some nextPermission =>
          let nextState : LocationState := {
            state with
            accessed := state.accessed || !relatedness.isForeign
            permission := nextPermission
          }
          if isProtected && nextState.accessed && transition.producesDisabled then
            .Error nextState (.ProtectedDisabled state.permission)
          else if !nextState.possible then
            .PossibleInvariantFailure nextState
          else .Success nextState transition

/-- A forbidden child access leaves every part of the location state intact. -/
theorem performAccess_child_forbidden_unchanged (state : LocationState)
    (accessKind : AccessKind) (isProtected : Bool)
    (h : performAccessTransition accessKind .LocalAccess state.permission isProtected =
      .UndefinedBehavior) :
    performAccess state accessKind .LocalAccess isProtected =
      .Error state (.ChildAccessForbidden state.permission) := by
  simp [performAccess, h]

/-- A foreign access to an unprotected Disabled node changes neither its
permission, accessed bit nor SIFA. The wildcard postorder visitor uses this
fact only after retaining the effects of all children. -/
theorem performAccess_foreign_disabled_unprotected (accessed : Bool)
    (sifa : IdempotentForeignAccess) (kind : AccessKind) :
    performAccess ⟨.Disabled, accessed, sifa⟩ kind .ForeignAccess false =
      .Success ⟨.Disabled, accessed, sifa⟩ ⟨.Disabled, .Disabled⟩ := by
  cases kind <;> cases accessed <;> rfl

/-- A foreign access to an unprotected Cell has no permission/accessed/SIFA
transition. This does not authorize omitting recordNewAccess when its skip
predicate says Recurse. -/
theorem performAccess_foreign_cell_unprotected (accessed : Bool)
    (sifa : IdempotentForeignAccess) (kind : AccessKind) :
    performAccess ⟨.Cell, accessed, sifa⟩ kind .ForeignAccess false =
      .Success ⟨.Cell, accessed, sifa⟩ ⟨.Cell, .Cell⟩ := by
  cases kind <;> cases accessed <;> rfl

/-- The restricted postorder repair only omits transitions that are no-ops.
The caller separately requires exact Foreign relatedness and no protector. -/
theorem foreign_disabled_or_cell_noop (state : LocationState) (kind : AccessKind)
    (permission : state.permission = .Disabled ∨ state.permission = .Cell) :
    performAccess state kind .ForeignAccess false =
      .Success state ⟨state.permission,state.permission⟩ := by
  cases state with
  | mk p accessed sifa =>
    rcases permission with rfl | rfl
    · exact performAccess_foreign_disabled_unprotected accessed sifa kind
    · exact performAccess_foreign_cell_unprotected accessed sifa kind

/-- The complete foreign-Write same-state normal-return class for all
protection/accessed combinations. It preserves the whole state for foreign Read. Protection is
retained: an accessed Disabled node and every ReservedIM node reject a held
protector. This Boolean contains no operation-success premise. -/
def foreignWriteNoop (state : LocationState) (isProtected : Bool) : Bool :=
  state.permission == .Cell ||
    (state.permission.isDisabled && (!isProtected || !state.accessed)) ||
    (state.permission == .ReservedIM && !isProtected)

theorem foreignWriteNoop_iff (state : LocationState) (isProtected : Bool) :
    state.foreignWriteNoop isProtected = true ↔
      state.permission = .Cell ∨
      (state.permission = .Disabled ∧ (isProtected = false ∨ state.accessed = false)) ∨
      (state.permission = .ReservedIM ∧ isProtected = false) := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission <;> cases accessed <;> cases isProtected <;>
    simp [foreignWriteNoop,Permission.isDisabled]

/-- Every field, including SIFA, is unchanged for either access kind. -/
theorem performAccess_foreignWriteNoop (state : LocationState) (kind : AccessKind)
    (isProtected : Bool) (eligible : state.foreignWriteNoop isProtected = true) :
    state.performAccess kind .ForeignAccess isProtected =
      .Success state ⟨state.permission,state.permission⟩ := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission <;> cases accessed <;> cases isProtected <;> cases kind <;>
    simp_all [foreignWriteNoop,Permission.isDisabled]
  all_goals rfl

/-- The postorder skip condition only replaces an old assertion branch;
it does not bypass an old successful SIFA update. -/
theorem recordNewAccess_debug_of_skip (state : LocationState) (kind : AccessKind)
    (relatedness : AccessRelatedness)
    (skip : state.skipIfKnownNoop kind relatedness = .SkipSelfAndChildren) :
    state.recordNewAccess kind relatedness = .DebugAssertion := by
  simp [recordNewAccess,skip]

end LocationState

end Tree

end Miri.TreeBorrows
