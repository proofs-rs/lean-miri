import duplicate_prefix.S05NoCutoffOwnershipBridge

namespace DuplicatePrefix.S05PrimaryRootOwnership
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposureAncestorFold
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- At an unclamped physical primary root, every positive residual count
classifies Local. No foreign permission is consumed at this query. -/
theorem root_local (count : Nat) (positive : 0 < count) :
    classify count count false false = some .LocalAccess := by
  simp [classify, show count ≠ 0 by omega]

/-- Raw no-cutoff primary ownership. Foreign table rights exclude the primary
root; local rights depend only on positive exposed contributor cardinality.
This is a sufficient snapshot class, not ordinary-validity coverage. -/
structure Ownership (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) where
  area : GeneralBorrowWildcardControlStack.Support tree root
  covers : ∀ query, area.contains query → Covers tree.nodes root query
  possible : ∀ query node, area.contains query → tree.nodes.get query = some node →
    ((location.perms.get query).getD node.defaultLocationState).possible = true
  foreign : ∀ query node, area.contains query → tree.nodes.get query = some node → query ≠ root → ∀ kind,
    DuplicatePrefixScalarAuthorization.Compatible
      ((location.perms.get query).getD node.defaultLocationState) kind .ForeignAccess (protections.contains node.tag)
  localRights : ∀ query node, area.contains query → tree.nodes.get query = some node → ∀ kind,
    0 < cardinality tree.nodes (effective location protections) query kind →
    DuplicatePrefixScalarAuthorization.Compatible
      ((location.perms.get query).getD node.defaultLocationState) kind .LocalAccess (protections.contains node.tag)
  primary : ∃ witness node, area.contains witness ∧ tree.nodes.get witness = some node ∧
    node.isExposed = true ∧ (effective location protections witness node).allows .Write = true

/-- The weaker primary packet proves the existing callback capability for both
kinds. All legal no-cutoff residual masks are empty, so root_local applies to
all pairs, including the protected Unique root case. -/
theorem authorization (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rights : Ownership tree location protections root)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (coherent : LocationCoherent tree location protections) (short : tree.nodes.size < 65536)
    (kind : AccessKind) : Authorization tree location protections root 0 none kind rights.area.contains := by
  have counts (query : UniIndex) : GeneralBorrowWildcardRelatednessBounds.count location.exposedCache query kind =
      cardinality tree.nodes (effective location protections) query kind :=
by
      cases kind with
      | Read => exact nat_exact location.exposedCache tree.nodes (effective location protections) coherent short query .Read
      | Write => exact nat_exact location.exposedCache tree.nodes (effective location protections) coherent short query .Write
  have eligible : ∃ witness node, rights.area.contains witness ∧ tree.nodes.get witness = some node ∧
      Supports location protections witness node none kind := by
    obtain ⟨witness,node,inside,present,exposed,write⟩ := rights.primary
    refine ⟨witness,node,inside,present,exposed,?_,by simp⟩
    change (effective location protections witness node).allows kind = true
    cases level : effective location protections witness node <;> cases kind <;>
      simp_all [WildcardAccessLevel.allows]
  obtain ⟨witness,node,inside,present,supported⟩ := eligible
  have path := GeneralBorrowWildcardControlWitness.path_of_covers tree depth root witness node present (rights.covers witness inside)
  have total := GeneralBorrowResidualPrimaryWitness.positive tree location protections depth none kind []
    (empty_removal tree location protections none kind) root witness node present supported path
  rw [residual_empty] at total
  have snapshot : Snapshot tree location protections root 0 none kind rights.area.contains := by
    refine ⟨?_,fun _ => ⟨witness,node,inside,present,supported⟩⟩
    intro query queryNode included found
    have possible := rights.possible query queryNode included found
    have positiveCount : 0 < GeneralBorrowWildcardRelatednessBounds.count location.exposedCache root kind := by
      rw [counts]; exact total
    have nonabsent : relation location root query queryNode none kind 0 ≠ none := by
      simp only [relation, aboveMaximum, bne_self_eq_false]
      unfold classify
      simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
      simp only [beq_iff_eq, show GeneralBorrowWildcardRelatednessBounds.count location.exposedCache root kind ≠ 0 by omega, ite_false]
      split
      · simp
      · split <;> simp
    cases classified : relation location root query queryNode none kind 0 with
    | none => exact False.elim (nonabsent classified)
    | some related =>
      cases related with
      | EitherAccess => exact possible
      | ForeignAccess =>
        refine ⟨possible,Or.inr (rights.foreign query queryNode included found ?_ kind)⟩
        intro same
        subst query
        have localClass : relation location root root queryNode none kind 0 = some .LocalAccess := by
          simpa [relation,aboveMaximum] using root_local _ positiveCount
        rw [localClass] at classified
        cases classified
      | LocalAccess =>
        have positiveLocal : 0 < cardinality tree.nodes (effective location protections) query kind := by
          rw [←counts]
          simp only [relation,aboveMaximum,bne_self_eq_false] at classified
          unfold classify at classified
          simp only [Bool.false_eq_true,ite_false,Nat.add_zero] at classified
          by_cases zero : GeneralBorrowWildcardRelatednessBounds.count location.exposedCache root kind = 0
          · simp [zero] at classified
          · by_cases equal : GeneralBorrowWildcardRelatednessBounds.count location.exposedCache root kind = GeneralBorrowWildcardRelatednessBounds.count location.exposedCache query kind
            · omega
            · simp [zero,equal] at classified
              split at classified <;> simp_all
        exact ⟨possible,Or.inr (rights.localRights query queryNode included found kind positiveLocal)⟩
  exact DuplicatePrefixResidualSupportSnapshotBridge.of_snapshot tree location protections root 0 none kind rights.area.contains
    snapshot rights.area.rooted rights.area.present rights.area.children rights.covers coherent short
    (fun removed legal => no_maximum_removal_empty tree location protections kind removed legal)

/-- Exact table separation: a protected active Unique state has both local
rights, while the old unconditional foreign Read requirement rejects it. This
is a scalar snapshot fact, without any Rust reachability claim. -/
theorem protected_unique (cache : IdempotentForeignAccess) :
    (∀ kind, DuplicatePrefixScalarAuthorization.Compatible
      ⟨.Unique, true, cache⟩ kind .LocalAccess true) ∧
    ¬ DuplicatePrefixScalarAuthorization.Compatible
      ⟨.Unique, true, cache⟩ .Read .ForeignAccess true := by
  constructor
  · intro kind
    cases kind <;> simp [DuplicatePrefixScalarAuthorization.Compatible,
      GeneralBorrowProtectedReadCompatible.Compatible,
      GeneralBorrowExposedConditionalWritePermissions.Compatible,
      LocationState.possible,Permission.isUnique]
  · simp [DuplicatePrefixScalarAuthorization.Compatible,
      GeneralBorrowProtectedReadCompatible.Compatible]

end DuplicatePrefix.S05PrimaryRootOwnership
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S05PrimaryRootOwnership.root_local,
      ``DuplicatePrefix.S05PrimaryRootOwnership.authorization,
      ``DuplicatePrefix.S05PrimaryRootOwnership.protected_unique] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
