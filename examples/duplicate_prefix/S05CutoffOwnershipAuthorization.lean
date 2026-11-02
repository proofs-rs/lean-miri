import duplicate_prefix.S05CutoffOwnershipGeometry
import duplicate_prefix.S05WriteCacheContributorOwnership

namespace DuplicatePrefix.S05CutoffOwnershipAuthorization
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardParentTagOrder
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization DuplicatePrefixCallbackVisitAuthorization
open S05CutoffOwnershipGeometry S05WriteCacheContributorOwnership
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

private theorem unclamped_some (rootCount localCount : Nat) (virtual : Bool)
    (positive : 0 < rootCount + if virtual then 1 else 0) :
    classify rootCount localCount virtual false ≠ none := by
  cases virtual <;> by_cases rootZero : rootCount = 0 <;> by_cases same : rootCount = localCount <;>
    by_cases plusSame : rootCount+1 = localCount <;> by_cases localZero : localCount = 0 <;>
    simp_all [classify]

private theorem local_positive (rootCount localCount : Nat) (virtual foreign : Bool)
    (classified : classify rootCount localCount virtual foreign = some .LocalAccess) : 0 < localCount := by
  cases foreign <;> cases virtual <;> by_cases rootZero : rootCount = 0 <;> by_cases same : rootCount = localCount <;>
    by_cases plusSame : rootCount+1 = localCount <;> by_cases localZero : localCount = 0 <;>
    simp_all [classify] <;> omega

private theorem foreign_zero (rootCount localCount : Nat) (virtual : Bool)
    (classified : classify rootCount localCount virtual false = some .ForeignAccess) : localCount = 0 := by
  cases virtual <;> by_cases rootZero : rootCount = 0 <;> by_cases same : rootCount = localCount <;>
    by_cases plusSame : rootCount+1 = localCount <;> by_cases localZero : localCount = 0 <;>
    simp_all [classify]

private theorem zero_foreign (rootCount : Nat) (virtual : Bool)
    (positive : 0 < rootCount + if virtual then 1 else 0) :
    classify rootCount 0 virtual false = some .ForeignAccess := by
  cases virtual <;> by_cases rootZero : rootCount = 0 <;> simp_all [classify]

private theorem relation_present (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (rights : S05NoCutoffOwnershipBridge.Ownership tree location protections root position)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (witness : CutoffWitness tree location protections root position maximum rights.area.contains)
    (query : UniIndex) (node : TreeNode) (inside : rights.area.contains query) (present : tree.nodes.get query = some node)
    (kind : AccessKind) (removed : List UniIndex) (legal : Removal tree location protections maximum kind removed) :
    residualRelation tree location protections root query node maximum kind position removed ≠ none := by
  cases above : aboveMaximum node maximum with
  | true => rw [clamped_foreign tree location protections root position maximum rights depth order witness query node inside present above kind removed legal];simp
  | false =>
    simpa only [residualRelation,above] using unclamped_some
      (residualCount tree location protections kind removed root) (residualCount tree location protections kind removed query)
      (position != 0) (total_positive tree location protections root position maximum rights depth witness kind removed legal)

private theorem local_compatible (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (rights : S05NoCutoffOwnershipBridge.Ownership tree location protections root position)
    (query : UniIndex) (node : TreeNode) (inside : rights.area.contains query) (present : tree.nodes.get query = some node)
    (kind : AccessKind) (removed : List UniIndex)
    (classified : residualRelation tree location protections root query node maximum kind position removed = some .LocalAccess) :
    DuplicatePrefixScalarAuthorization.Compatible
      ((location.perms.get query).getD node.defaultLocationState) kind .LocalAccess (protections.contains node.tag) := by
  have positive := local_positive _ _ _ _ classified
  have bound : residualCount tree location protections kind removed query ≤
      cardinality tree.nodes (effective location protections) query kind := List.length_filter_le _ _
  exact S05NoCutoffOwnershipBridge.local_of_count tree location protections root position rights query node inside present kind (by omega)

/-- The same independent ownership tables and cutoff witness form Read query
pairs: Read has no removable contributors, so both masks are necessarily empty. -/
theorem read_authorization (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (rights : S05NoCutoffOwnershipBridge.Ownership tree location protections root position)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (witness : CutoffWitness tree location protections root position maximum rights.area.contains) :
    Authorization tree location protections root position maximum .Read rights.area.contains := by
  refine ⟨rights.area.rooted,rights.area.present,rights.area.children,rights.covers,?_,?_,witness_kind tree location protections root position maximum rights.area.contains witness .Read⟩
  · intro query node inside present
    exact (rights.foreign query node inside present .Write).1
  · intro before after legalBefore legalAfter _ query node inside present _
    have beforeEmpty := read_removal_empty tree location protections maximum before legalBefore
    have afterEmpty := read_removal_empty tree location protections maximum after legalAfter
    subst before
    subst after
    apply DuplicatePrefixResidualSupportSnapshotBridge.same_query
    have possible := (rights.foreign query node inside present .Write).1
    have nonabsent := relation_present tree location protections root position maximum rights depth order witness query node inside present .Read [] legalBefore
    cases classified : residualRelation tree location protections root query node maximum .Read position [] with
    | none => exact False.elim (nonabsent classified)
    | some related =>
      cases related with
      | EitherAccess => exact possible
      | ForeignAccess => exact ⟨possible,Or.inr (rights.foreign query node inside present .Read)⟩
      | LocalAccess => exact ⟨possible,Or.inr (local_compatible tree location protections root position maximum rights query node inside present .Read [] classified)⟩

/-- Arbitrary conservative Write removal pairs are closed under independent
snapshot ownership, cutoff geometry and nondroppable contributors below skips.
No Row, Authorization, operation outcome or NoUB is assumed. -/
theorem write_authorization (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (rights : S05NoCutoffOwnershipBridge.Ownership tree location protections root position)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (witness : CutoffWitness tree location protections root position maximum rights.area.contains)
    (stable : SkipStable tree location protections maximum rights.area.contains) :
    Authorization tree location protections root position maximum .Write rights.area.contains := by
  refine ⟨rights.area.rooted,rights.area.present,rights.area.children,rights.covers,?_,?_,witness_kind tree location protections root position maximum rights.area.contains witness .Write⟩
  · intro query node inside present
    exact (rights.foreign query node inside present .Write).1
  · intro before after legalBefore legalAfter _ query node inside present _
    let state := (location.perms.get query).getD node.defaultLocationState
    have possible : state.possible = true := (rights.foreign query node inside present .Write).1
    refine ⟨possible,?_⟩
    by_cases skipped : entrySkip state .Write (residualRelation tree location protections root query node maximum .Write position before) = true
    · exact Or.inl skipped
    · apply Or.inr
      have nonabsent := relation_present tree location protections root position maximum rights depth order witness query node inside present .Write after legalAfter
      cases classified : residualRelation tree location protections root query node maximum .Write position after with
      | none => exact False.elim (nonabsent classified)
      | some related =>
        cases related with
        | EitherAccess => trivial
        | LocalAccess =>
          exact ⟨by simp [skip,AccessRelatedness.isForeign],
            local_compatible tree location protections root position maximum rights query node inside present .Write after classified⟩
        | ForeignAccess =>
          refine ⟨?_,rights.foreign query node inside present .Write⟩
          cases skipForeign : skip state .Write .ForeignAccess with
          | false => rfl
          | true =>
            have entryForeign : residualRelation tree location protections root query node maximum .Write position before = some .ForeignAccess := by
              cases above : aboveMaximum node maximum with
              | true => exact clamped_foreign tree location protections root position maximum rights depth order witness query node inside present above .Write before legalBefore
              | false =>
                have zero := foreign_zero _ _ _ (by simpa only [residualRelation,above] using classified)
                have beforeStable := residual_stable tree location protections maximum rights.area.contains stable query node inside present skipForeign before legalBefore
                have afterStable := residual_stable tree location protections maximum rights.area.contains stable query node inside present skipForeign after legalAfter
                have beforeZero : residualCount tree location protections .Write before query = 0 := by omega
                have positive := total_positive tree location protections root position maximum rights depth witness .Write before legalBefore
                simpa only [residualRelation,above,beforeZero] using zero_foreign _ _ positive
            exact False.elim (skipped (by simpa only [entryForeign,entrySkip] using skipForeign))

/-- Physical parent-cache ordering and ordinary scalar consistency discharge
the added SkipStable ownership condition before any operation executes. -/
theorem write_of_cache_order (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (rights : S05NoCutoffOwnershipBridge.Ownership tree location protections root position)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (tagOrder : ParentTagOrder tree)
    (witness : CutoffWitness tree location protections root position maximum rights.area.contains)
    (cacheOrder : ParentCacheOrder tree location)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections) :
    Authorization tree location protections root position maximum .Write rights.area.contains :=
  write_authorization tree location protections root position maximum rights depth tagOrder witness
    (skip_stable tree location protections root position rights depth cacheOrder profile maximum)

end DuplicatePrefix.S05CutoffOwnershipAuthorization
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S05CutoffOwnershipAuthorization.read_authorization,
      ``DuplicatePrefix.S05CutoffOwnershipAuthorization.write_authorization,
      ``DuplicatePrefix.S05CutoffOwnershipAuthorization.write_of_cache_order] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
