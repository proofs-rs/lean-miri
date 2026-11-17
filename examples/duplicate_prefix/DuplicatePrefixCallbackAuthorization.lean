import duplicate_prefix.DuplicatePrefixScalarAuthorization
import duplicate_prefix.GeneralBorrowWildcardRelatednessBounds

namespace DuplicatePrefix.DuplicatePrefixCallbackAuthorization
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree

/-- Numeric specification of the current callback classification. The virtual
alternative is added in Nat, exactly as in the pinned Lean interpreter. This
definition refers to no access result, trace, or final-state condition. -/
def classify (rootCount localCount : Nat) (virtual onlyForeign : Bool) :
    Option WildcardAccessRelatedness :=
  let total := rootCount + if virtual then 1 else 0
  let relation := if total == 0 then none
    else if total == localCount then some .LocalAccess
    else if localCount == 0 then some .ForeignAccess
    else some .EitherAccess
  if onlyForeign then
    match relation with
    | some .LocalAccess | none => none
    | some .ForeignAccess | some .EitherAccess => some .ForeignAccess
  else relation

/-- The numeric specification agrees with the actual cache rule for both
access kinds, both root positions, and both tag-filter branches. -/
theorem classify_source (cache : ExposedCache) (root index : UniIndex)
    (kind : AccessKind) (virtual onlyForeign : Bool) :
    cache.accessRelatedness root index kind virtual onlyForeign =
      classify (GeneralBorrowWildcardRelatednessBounds.count cache root kind)
        (GeneralBorrowWildcardRelatednessBounds.count cache index kind) virtual onlyForeign := by
  cases kind <;> rfl

/-- A tag above the actual selected-root maximum is forced foreign. A wildcard
input has no such maximum. This is not the input descendant's tag bound. -/
def aboveMaximum (node : TreeNode) (maximum : Option BorTag) : Bool :=
  match maximum with
  | none => false
  | some tag => tag.value < node.tag.value

def relation (location : LocationTree) (root index : UniIndex) (node : TreeNode)
    (maximum : Option BorTag) (kind : AccessKind) (rootPosition : Nat) :
    Option WildcardAccessRelatedness :=
  classify (GeneralBorrowWildcardRelatednessBounds.count location.exposedCache root kind)
    (GeneralBorrowWildcardRelatednessBounds.count location.exposedCache index kind)
    (rootPosition != 0) (aboveMaximum node maximum)

theorem relation_source (location : LocationTree) (root index : UniIndex) (node : TreeNode)
    (maximum : Option BorTag) (kind : AccessKind) (rootPosition : Nat) :
    relation location root index node maximum kind rootPosition =
      location.exposedCache.accessRelatedness root index kind
        (rootPosition != 0) (aboveMaximum node maximum) :=
  (classify_source _ _ _ _ _ _).symm

/-- Data-only skip-cache query, separate from scalar transition permission.
In particular a disabled foreign row is skipped even if a scalar access would
reject its active protector. -/
def skip (state : LocationState) (kind : AccessKind) (related : AccessRelatedness) : Bool :=
  related.isForeign &&
    ((match IdempotentForeignAccess.canSkipForeignAccess state.idempotentForeignAccess
        (IdempotentForeignAccess.fromForeign kind) with
      | .Decision canSkip => canSkip
      | .DebugAssertion => false) || state.permission.isDisabled ||
        (state.permission.isFrozen && kind == .Read))

theorem skip_source (state : LocationState) (kind : AccessKind) (related : AccessRelatedness) :
    skip state kind related = true ↔
      state.skipIfKnownNoop kind related = .SkipSelfAndChildren := by
  cases related <;> simp [skip, LocationState.skipIfKnownNoop, AccessRelatedness.isForeign]
  split
  · rename_i canSkip _
    cases canSkip <;> cases disabled : state.permission.isDisabled <;> simp_all
  · cases disabled : state.permission.isDisabled <;> simp_all

def ExactQuery (state : LocationState) (kind : AccessKind) (related : AccessRelatedness) (held : Bool) : Prop :=
  state.possible = true ∧
    (skip state kind related = true ∨ DuplicatePrefixScalarAuthorization.Compatible state kind related held)

/-- Sufficient scalar authorization for one callback query. An Either query
does not execute a scalar transition, so it imposes no local/foreign ownership
condition. Possible is an independent runtime consistency condition. This is
a snapshot condition, not a complete reference-validity predicate. -/
def Scalar (state : LocationState) (kind : AccessKind) (held : Bool) :
    Option WildcardAccessRelatedness → Prop
  | none => False
  | some .LocalAccess => ExactQuery state kind .LocalAccess held
  | some .ForeignAccess => ExactQuery state kind .ForeignAccess held
  | some .EitherAccess => state.possible = true

def exactRelation : WildcardAccessRelatedness → Option AccessRelatedness
  | .LocalAccess => some .LocalAccess
  | .ForeignAccess => some .ForeignAccess
  | .EitherAccess => none

/-- The source visitor checks skip/record before a scalar transition. All
successful alternatives below are derived from the permission/skip data. -/
theorem scalar_visit (state : LocationState) (kind : AccessKind) (held : Bool)
    (related : WildcardAccessRelatedness) (exact : AccessRelatedness)
    (authorized : Scalar state kind held (some related))
    (relationEq : exactRelation related = some exact) :
    state.skipIfKnownNoop kind exact = .SkipSelfAndChildren ∨
    ∃ recorded next transition,
      state.recordNewAccess kind exact = .Recorded recorded ∧
      recorded.performAccess kind exact held = .Success next transition := by
  have raw : ExactQuery state kind exact held := by
    cases related <;> simp_all [exactRelation, Scalar]
  cases skip : state.skipIfKnownNoop kind exact with
  | SkipSelfAndChildren => exact .inl rfl
  | Recurse =>
    have compatible : DuplicatePrefixScalarAuthorization.Compatible state kind exact held := by
      rcases raw.2 with skipped | compatible
      · have impossible := (skip_source _ _ _).mp skipped
        rw [skip] at impossible
        cases impossible
      · exact compatible
    let recorded := {state with idempotentForeignAccess := (
      IdempotentForeignAccess.recordNew state.idempotentForeignAccess
        (IdempotentForeignAccess.fromAccessAndRelatedness kind exact))}
    have inherited : DuplicatePrefixScalarAuthorization.Compatible recorded kind exact held := by
      cases kind <;> cases exact <;> exact compatible
    have possible : recorded.possible = true := raw.1
    obtain ⟨next, transition, access⟩ := (DuplicatePrefixScalarAuthorization.compatible_iff _ _ _ _ possible).mp inherited
    exact .inr ⟨recorded, next, transition, by simp [LocationState.recordNewAccess, skip, recorded], access⟩

theorem either_no_scalar_transition : exactRelation .EitherAccess = none := rfl

/-- The exact raw exposed-support test used by the callback's witness check.
It is separate from Scalar: cache classification alone supplies no witness. -/
def Supports (location : LocationTree) (protections : ProtectedTags)
    (index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (kind : AccessKind) : Prop :=
  node.isExposed = true ∧
  (((location.perms.get index).getD node.defaultLocationState).permission.strongestAllowedLocalAccess
    (protections.contains node.tag)).allows kind = true ∧
  (maximum.isNone || maximum.any (fun tag => tag.value >= node.tag.value)) = true

theorem supports_source (location : LocationTree) (protections : ProtectedTags)
    (index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (kind : AccessKind) :
    Supports location protections index node maximum kind ↔
      (node.isExposed &&
        (((location.perms.get index).getD node.defaultLocationState).permission.strongestAllowedLocalAccess
          (protections.contains node.tag)).allows kind &&
        (maximum.isNone || maximum.any (fun tag => tag.value >= node.tag.value))) = true := by
  simp [Supports, Bool.and_eq_true, and_assoc]

set_option autoImplicit false in
/-- Data-only authorization on a specified callback support at ONE location
snapshot. The support must later be connected to the actual root traversal;
the required source-derived preservation through child/cache updates is not
asserted here. In particular this record is not complete MutableU8Slice. -/
structure Snapshot (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (kind : AccessKind)
    (support : UniIndex → Prop) : Prop where
  scalar : ∀ index node, support index → tree.nodes.get index = some node →
    Scalar ((location.perms.get index).getD node.defaultLocationState) kind
      (protections.contains node.tag) (relation location root index node maximum kind rootPosition)
  witness : rootPosition = 0 → ∃ index node, support index ∧ tree.nodes.get index = some node ∧
    Supports location protections index node maximum kind

/-- Snapshot authorization supplies the actual cache classification and the
entire per-query successful visitor alternative. No classification or operation
success is assumed by the caller. This is still one query at the given current
location; threading authorization through child/cache changes is separate. -/
theorem Snapshot.query {tree : BorrowTree} {location : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {rootPosition : Nat} {maximum : Option BorTag} {kind : AccessKind}
    {support : UniIndex → Prop}
    (snapshot : Snapshot tree location protections root rootPosition maximum kind support)
    (index : UniIndex) (node : TreeNode) (supported : support index)
    (present : tree.nodes.get index = some node) :
    ∃ related,
      location.exposedCache.accessRelatedness root index kind
        (rootPosition != 0) (aboveMaximum node maximum) = some related ∧
      (related = .EitherAccess ∨ ∃ exact,
        exactRelation related = some exact ∧
        (((location.perms.get index).getD node.defaultLocationState).skipIfKnownNoop kind exact =
          .SkipSelfAndChildren ∨ ∃ recorded next transition,
          ((location.perms.get index).getD node.defaultLocationState).recordNewAccess kind exact =
            .Recorded recorded ∧
          recorded.performAccess kind exact (protections.contains node.tag) = .Success next transition)) := by
  have authorized := snapshot.scalar index node supported present
  cases classified : relation location root index node maximum kind rootPosition with
  | none => simp [classified, Scalar] at authorized
  | some related =>
    have source : location.exposedCache.accessRelatedness root index kind
        (rootPosition != 0) (aboveMaximum node maximum) = some related :=
      (relation_source _ _ _ _ _ _ _).symm.trans classified
    refine ⟨related, source, ?_⟩
    rw [classified] at authorized
    cases related with
    | EitherAccess => exact .inl rfl
    | LocalAccess => exact .inr ⟨.LocalAccess, rfl, scalar_visit _ _ _ _ _ authorized rfl⟩
    | ForeignAccess => exact .inr ⟨.ForeignAccess, rfl, scalar_visit _ _ _ _ _ authorized rfl⟩

/-- Physical root position zero requires a real supporting exposed reference.
Its exact visitor witness Boolean follows from the raw data field. Preservation
until the postorder witness test remains a separate obligation. -/
theorem Snapshot.physical_witness {tree : BorrowTree} {location : LocationTree}
    {protections : ProtectedTags} {root : UniIndex} {rootPosition : Nat}
    {maximum : Option BorTag} {kind : AccessKind} {support : UniIndex → Prop}
    (snapshot : Snapshot tree location protections root rootPosition maximum kind support)
    (physical : rootPosition = 0) :
    ∃ index node, support index ∧ tree.nodes.get index = some node ∧
      (node.isExposed &&
        (((location.perms.get index).getD node.defaultLocationState).permission.strongestAllowedLocalAccess
          (protections.contains node.tag)).allows kind &&
        (maximum.isNone || maximum.any (fun tag => tag.value >= node.tag.value))) = true := by
  obtain ⟨index, node, supported, present, witness⟩ := snapshot.witness physical
  exact ⟨index, node, supported, present, (supports_source _ _ _ _ _ _).mp witness⟩

/-- A scalar illustration of why Either must not be replaced with Local in a
general authorization definition: a frozen node is harmless on Either Write,
even when its local Write would be forbidden. This is not a whole-call example
or a claim that the supplied counts alone establish cache coherence. -/
theorem either_not_local_write :
    classify 1 1 true false = some .EitherAccess ∧
    Scalar ⟨.Frozen, true, .None⟩ .Write true (some .EitherAccess) ∧
    ¬ DuplicatePrefixScalarAuthorization.Compatible ⟨.Frozen, true, .None⟩ .Write .LocalAccess true := by
  simp [classify, Scalar, LocationState.possible, DuplicatePrefixScalarAuthorization.Compatible,
    GeneralBorrowExposedConditionalWritePermissions.Compatible]

end DuplicatePrefix.DuplicatePrefixCallbackAuthorization
