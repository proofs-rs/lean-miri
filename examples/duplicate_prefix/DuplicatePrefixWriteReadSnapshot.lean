import duplicate_prefix.DuplicatePrefixCrossKindQueryGuard
namespace DuplicatePrefix.DuplicatePrefixWriteReadSnapshot
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization GeneralBorrowExposureCardinality DuplicatePrefixCrossKindQueryGuard
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-- Cached foreign Write skipping also permits foreign Read skipping. -/
theorem write_skip_read_skip (state : LocationState)
    (skipped : skip state .Write .ForeignAccess = true) : skip state .Read .ForeignAccess = true := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted => cases conflicted <;> cases sifa <;>
      simp_all [skip,AccessRelatedness.isForeign,IdempotentForeignAccess.fromForeign,
        IdempotentForeignAccess.canSkipForeignAccess,IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,
        IdempotentForeignAccess.rank,Permission.isDisabled,Permission.isFrozen]
  | Cell | ReservedIM | Unique | Frozen | Disabled => cases sifa <;>
      simp_all [skip,AccessRelatedness.isForeign,IdempotentForeignAccess.fromForeign,
        IdempotentForeignAccess.canSkipForeignAccess,IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,
        IdempotentForeignAccess.rank,Permission.isDisabled,Permission.isFrozen]

theorem compatible_write_read (state : LocationState) (related : AccessRelatedness) (held : Bool)
    (write : DuplicatePrefixScalarAuthorization.Compatible state .Write related held) :
    DuplicatePrefixScalarAuthorization.Compatible state .Read related held := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted => cases conflicted <;> cases accessed <;> cases related <;> cases held <;>
      simp_all [DuplicatePrefixScalarAuthorization.Compatible,GeneralBorrowExposedConditionalWritePermissions.Compatible,
        GeneralBorrowProtectedReadCompatible.Compatible,LocationState.possible,Permission.isUnique]
  | Cell | ReservedIM | Unique | Frozen | Disabled => cases accessed <;> cases related <;> cases held <;>
      simp_all [DuplicatePrefixScalarAuthorization.Compatible,GeneralBorrowExposedConditionalWritePermissions.Compatible,
        GeneralBorrowProtectedReadCompatible.Compatible,LocationState.possible,Permission.isUnique]

/-- Every raw Write scalar snapshot is a Read scalar snapshot at the SAME
optional classification, including cached skips and Either. -/
theorem scalar (state : LocationState) (held : Bool) (query : Option WildcardAccessRelatedness)
    (write : DuplicatePrefixCallbackAuthorization.Scalar state .Write held query) :
    DuplicatePrefixCallbackAuthorization.Scalar state .Read held query := by
  cases query with
  | none => exact False.elim write
  | some related =>
    cases related with
    | EitherAccess => exact write
    | LocalAccess =>
      refine ⟨write.1,?_⟩
      rcases write.2 with skipped | compatible
      · simp [skip,AccessRelatedness.isForeign] at skipped
      · exact .inr (compatible_write_read _ .LocalAccess held compatible)
    | ForeignAccess =>
      refine ⟨write.1,?_⟩
      rcases write.2 with skipped | compatible
      · exact .inl (write_skip_read_skip state skipped)
      · exact .inr (compatible_write_read _ .ForeignAccess held compatible)

private theorem exact_count (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (coherent : LocationCoherent tree location protections) (short : tree.nodes.size < 65536)
    (query : UniIndex) (kind : AccessKind) : GeneralBorrowWildcardRelatednessBounds.count location.exposedCache query kind =
      cardinality tree.nodes (effective location protections) query kind := by
  have exact := nat_exact location.exposedCache tree.nodes (effective location protections) coherent short query kind
  cases kind <;> exact exact

private theorem classify_clamped (rootCount localCount : Nat) (virtual : Bool) :
    classify rootCount localCount virtual true = some .ForeignAccess ∨ classify rootCount localCount virtual true = none := by
  cases virtual <;> by_cases rootZero : rootCount = 0 <;> by_cases equal : rootCount = localCount <;>
    by_cases plusEqual : rootCount+1 = localCount <;> by_cases localZero : localCount = 0 <;>
    simp_all [classify] <;> omega

private theorem classify_zero_local (rootCount : Nat) (virtual : Bool) :
    classify rootCount 0 virtual false = some .ForeignAccess ∨ classify rootCount 0 virtual false = none := by
  cases virtual <;> by_cases rootZero : rootCount = 0 <;> simp [classify,rootZero]

/-- Foreign Read permits only Foreign or absent Write classification. A tag
clamp may make Write absent; without a clamp, Read-local zero implies Write-local zero. -/
theorem foreign_read_write (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (position : Nat)
    (coherent : LocationCoherent tree location protections) (short : tree.nodes.size < 65536)
    (foreign : relation location root index node maximum .Read position = some .ForeignAccess) :
    relation location root index node maximum .Write position = some .ForeignAccess ∨
      relation location root index node maximum .Write position = none := by
  have counts := exact_count tree location protections coherent short
  have localLe := write_cardinality_le_read tree.nodes (effective location protections) index
  by_cases clamp : aboveMaximum node maximum = true
  · simp only [relation,counts,clamp]
    exact classify_clamped _ _ _
  · have unclamped : aboveMaximum node maximum = false := Bool.eq_false_iff.mpr clamp
    have readZero : cardinality tree.nodes (effective location protections) index .Read = 0 := by
      by_cases zero : cardinality tree.nodes (effective location protections) index .Read = 0
      · exact zero
      have positive : 0 < cardinality tree.nodes (effective location protections) index .Read := by omega
      have raw : classify (cardinality tree.nodes (effective location protections) root .Read)
          (cardinality tree.nodes (effective location protections) index .Read) (position != 0) (aboveMaximum node maximum) = some .ForeignAccess := by
        simpa only [relation,counts] using foreign
      have yes := DuplicatePrefixResidualWriteTransition.classify_foreign_above _ _ _ _ positive raw
      rw [unclamped] at yes;cases yes
    have writeZero : cardinality tree.nodes (effective location protections) index .Write = 0 := by omega
    simp only [relation,counts,unclamped,writeZero]
    exact classify_zero_local _ _

/-- Exhaustive absence alternatives under actual root dominance. -/
theorem classify_none (rootCount localCount : Nat) (virtual clamp : Bool)
    (bounded : localCount ≤ rootCount) (absent : classify rootCount localCount virtual clamp = none) :
    (virtual = false ∧ rootCount = 0) ∨ (virtual = false ∧ clamp = true ∧ rootCount = localCount) := by
  cases virtual <;> cases clamp <;>
    by_cases rootZero : rootCount = 0 <;> by_cases equal : rootCount = localCount <;>
    by_cases plusEqual : rootCount+1 = localCount <;> by_cases localZero : localCount = 0 <;>
    simp_all [classify] <;> omega

/-- Read absence also means Write absence. In the clamped positive case this
uses actual contributor-list equality, not merely inequalities of counters. -/
theorem none_read_write (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (position : Nat)
    (coherent : LocationCoherent tree location protections) (short : tree.nodes.size < 65536)
    (covers : Covers tree.nodes root index)
    (absent : relation location root index node maximum .Read position = none) :
    relation location root index node maximum .Write position = none := by
  have counts := exact_count tree location protections coherent short
  have bound := cardinality_dominates tree.nodes (effective location protections) root index .Read covers
  have raw : classify (cardinality tree.nodes (effective location protections) root .Read)
      (cardinality tree.nodes (effective location protections) index .Read) (position != 0) (aboveMaximum node maximum) = none := by
    simpa only [relation,counts] using absent
  rcases classify_none _ _ _ _ bound raw with ⟨physical,zero⟩ | ⟨physical,clamp,equal⟩
  · have writeZero : cardinality tree.nodes (effective location protections) root .Write = 0 := by
      have le := write_cardinality_le_read tree.nodes (effective location protections) root
      omega
    simp [relation,counts,physical,writeZero,classify]
  · have lists := write_contributors_equal tree.nodes (effective location protections) root index covers equal
    have equalWrite : cardinality tree.nodes (effective location protections) root .Write = cardinality tree.nodes (effective location protections) index .Write := congrArg List.length lists
    by_cases writeZero : cardinality tree.nodes (effective location protections) index .Write = 0 <;>
      simp [relation,counts,physical,clamp,equalWrite,classify,writeZero]

/-- Full raw Write Snapshot supplies a Read Snapshot on the same state. Source
Read/Write classifications need not agree: the finite contributor guards
connect exact queries, and the original Write witness also supports Read.
This is data conversion; a later execution closure derives its input snapshot. -/
theorem snapshot (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (write : Snapshot tree location protections root position maximum .Write support)
    (coherent : LocationCoherent tree location protections) (short : tree.nodes.size < 65536)
    (covers : ∀ index, support index → Covers tree.nodes root index) :
    Snapshot tree location protections root position maximum .Read support := by
  refine ⟨?_,?_⟩
  · intro index node included present
    have writeScalar := write.scalar index node included present
    cases readQuery : relation location root index node maximum .Read position with
    | none =>
      have writeNone := none_read_write tree location protections root index node maximum position coherent short (covers index included) readQuery
      simp [writeNone,DuplicatePrefixCallbackAuthorization.Scalar] at writeScalar
    | some related =>
      cases related with
      | LocalAccess =>
        rcases local_read_write tree location protections root index node maximum position coherent short (covers index included) readQuery with writeLocal | writeNone
        · rw [writeLocal] at writeScalar
          exact scalar _ _ _ writeScalar
        · simp [writeNone,DuplicatePrefixCallbackAuthorization.Scalar] at writeScalar
      | ForeignAccess =>
        rcases foreign_read_write tree location protections root index node maximum position coherent short readQuery with writeForeign | writeNone
        · rw [writeForeign] at writeScalar
          exact scalar _ _ _ writeScalar
        · simp [writeNone,DuplicatePrefixCallbackAuthorization.Scalar] at writeScalar
      | EitherAccess =>
        exact DuplicatePrefixResidualSupportSnapshotBridge.scalar_possible _ .Write _ _ writeScalar
  · intro physical
    obtain ⟨index,node,included,present,eligible⟩ := write.witness physical
    refine ⟨index,node,included,present,eligible.1,?_,eligible.2.2⟩
    have allows := eligible.2.1
    change (effective location protections index node).allows .Write = true at allows
    change (effective location protections index node).allows .Read = true
    cases level : (effective location protections index node) <;> simp_all [WildcardAccessLevel.allows]
end DuplicatePrefix.DuplicatePrefixWriteReadSnapshot
