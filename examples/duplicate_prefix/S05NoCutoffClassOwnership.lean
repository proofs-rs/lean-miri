import duplicate_prefix.S05NoCutoffOwnershipBridge
import duplicate_prefix.BoolDestinationWriteOnlyAdapter
import duplicate_prefix.GeneralBorrowStructuralHistoryState

namespace DuplicatePrefix.S05NoCutoffClassOwnership
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposureAncestorFold
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- Raw no-cutoff ownership for all root positions. Foreign Write rights apply
only to zero-support cones; local Write rights apply only to full-support cones.
Intermediate positive cones require only possible scalar states.
This is a sufficient snapshot class, not ordinary-validity coverage. -/
structure Ownership (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) where
  area : GeneralBorrowWildcardControlStack.Support tree root
  covers : ∀ query, area.contains query → Covers tree.nodes root query
  possible : ∀ query node, area.contains query → tree.nodes.get query = some node →
    ((location.perms.get query).getD node.defaultLocationState).possible = true
  foreign : ∀ query node, area.contains query → tree.nodes.get query = some node →
    cardinality tree.nodes (effective location protections) query .Write = 0 →
    DuplicatePrefixScalarAuthorization.Compatible
      ((location.perms.get query).getD node.defaultLocationState) .Write .ForeignAccess (protections.contains node.tag)
  localRights : ∀ query node, area.contains query → tree.nodes.get query = some node →
    cardinality tree.nodes (effective location protections) query .Write =
      cardinality tree.nodes (effective location protections) root .Write + (if position != 0 then 1 else 0) →
    DuplicatePrefixScalarAuthorization.Compatible
      ((location.perms.get query).getD node.defaultLocationState) .Write .LocalAccess (protections.contains node.tag)
  primary : position = 0 → ∃ witness node, area.contains witness ∧ tree.nodes.get witness = some node ∧
    node.isExposed = true ∧ (effective location protections witness node).allows .Write = true

/-- No-cutoff removals are empty. Numeric contributor classes therefore
supply actual Write callback authorization without unconditional rights for
Local, Foreign and Either at the same node. -/
theorem authorization (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (rights : Ownership tree location protections root position)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (coherent : LocationCoherent tree location protections) (short : tree.nodes.size < 65536) :
    Authorization tree location protections root position none .Write rights.area.contains := by
  have counts (query : UniIndex) : GeneralBorrowWildcardRelatednessBounds.count location.exposedCache query .Write =
      cardinality tree.nodes (effective location protections) query .Write :=
    nat_exact location.exposedCache tree.nodes (effective location protections) coherent short query .Write
  have eligible : position = 0 → ∃ witness node, rights.area.contains witness ∧ tree.nodes.get witness = some node ∧
      Supports location protections witness node none .Write := by
    intro primary
    obtain ⟨witness,node,inside,present,exposed,write⟩ := rights.primary primary
    exact ⟨witness,node,inside,present,exposed,write,by simp⟩
  have total : 0 < cardinality tree.nodes (effective location protections) root .Write +
      (if position != 0 then 1 else 0) := by
    by_cases primary : position = 0
    · obtain ⟨witness,node,inside,present,supported⟩ := eligible primary
      have path := GeneralBorrowWildcardControlWitness.path_of_covers tree depth root witness node present (rights.covers witness inside)
      have positive := GeneralBorrowResidualPrimaryWitness.positive tree location protections depth none .Write []
        (empty_removal tree location protections none .Write) root witness node present supported path
      rw [residual_empty] at positive
      simpa only [primary,bne_self_eq_false,Bool.false_eq_true,ite_false,Nat.add_zero] using positive
    · simp only [show (position != 0) = true by simp [primary],ite_true]
      omega
  have snapshot : Snapshot tree location protections root position none .Write rights.area.contains := by
    refine ⟨?_,eligible⟩
    intro query node included found
    have possible := rights.possible query node included found
    have numeric := total
    rw [←counts root] at numeric
    generalize countRoot : GeneralBorrowWildcardRelatednessBounds.count location.exposedCache root .Write = rootCount at numeric
    generalize countLocal : GeneralBorrowWildcardRelatednessBounds.count location.exposedCache query .Write = localCount
    have rootExact : cardinality tree.nodes (effective location protections) root .Write = rootCount := by rw [←counts root,countRoot]
    have localExact : cardinality tree.nodes (effective location protections) query .Write = localCount := by rw [←counts query,countLocal]
    have localRights := rights.localRights query node included found
    have foreignRights := rights.foreign query node included found
    simp only [rootExact,localExact] at localRights foreignRights
    unfold relation classify
    simp only [aboveMaximum, Bool.false_eq_true, ite_false, countRoot, countLocal]
    by_cases zero : rootCount + (if position != 0 then 1 else 0) = 0
    · omega
    · simp only [beq_iff_eq,zero,ite_false]
      by_cases full : rootCount + (if position != 0 then 1 else 0) = localCount
      · simp only [full,ite_true]
        exact ⟨possible,Or.inr (localRights full.symm)⟩
      · simp only [full,ite_false]
        by_cases empty : localCount = 0
        · simp only [empty,ite_true]
          exact ⟨possible,Or.inr (foreignRights empty)⟩
        · simp only [empty,ite_false]
          exact possible
  exact DuplicatePrefixResidualSupportSnapshotBridge.of_snapshot tree location protections root position none .Write rights.area.contains
    snapshot rights.area.rooted rights.area.present rights.area.children rights.covers coherent short
    (fun removed legal => no_maximum_removal_empty tree location protections .Write removed legal)

/-- Complete the actual wildcard row using Write rights only. The existing
Write-to-Read snapshot theorem supplies protector Read authorization. -/
theorem row (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (coherent : LocationCoherent tree location protections) (short : tree.nodes.size < 65536)
    (ownership : ∀ position, (valid : position < tree.roots.size) →
      Nonempty (Ownership tree location protections tree.roots[position] position)) :
    DuplicatePrefixBorrowAuthorization.Row tree location protections none none none := by
  apply BoolDestinationWriteOnlyAdapter.WriteRow.complete (coherent := coherent) (short := short)
  refine {
    wildcard := fun _ => rfl
    rootPath := ?_
    rootPresent := ?_
    cutoff := rfl
    normal := ?_
    callbacks := ?_ }
  · intro anchor impossible; cases impossible
  · intro root impossible; cases impossible
  · intro anchor impossible; cases impossible
  · intro position valid _
    obtain ⟨rights⟩ := ownership position valid
    exact ⟨rights.area.contains,authorization tree location protections _ position rights depth coherent short⟩

/-- The existing positive wildcard capability consumed by the call contract,
formed from range-local raw class rights. Graph/resource/coherence and physical
window bounds remain explicit; ordinary call-time coverage remains separate. -/
theorem positive (tree : BorrowTree) (protections : ProtectedTags) (offset len : UInt64)
    (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (short : tree.nodes.size < 65536) (positiveLength : 0 < len.toNat)
    (bounds : offset.toNat + len.toNat ≤ tree.locations.size.bytes.toNat)
    (roots : 0 < tree.roots.size)
    (ownership : GeneralRangeMapOrigins.OwnedOn
      (fun location => ∀ position, (valid : position < tree.roots.size) →
        Nonempty (Ownership tree location protections tree.roots[position] position))
      offset (offset + len) tree.locations)
    (coherent : GeneralRangeMapOrigins.OwnedOn
      (fun location => LocationCoherent tree location protections)
      offset (offset + len) tree.locations) :
    DuplicatePrefixBorrowAuthorization.Positive tree protections none none none offset len := by
  obtain ⟨depth⟩ := graph.depth
  refine {
    positive := positiveLength
    bounds := bounds
    sourcePresent := ?_
    wildcardRoot := fun _ => roots
    rows := ?_ }
  · intro anchor impossible; cases impossible
  · intro position valid nonempty start stop
    exact ⟨row tree _ protections depth (coherent position valid nonempty start stop) short
      (ownership position valid nonempty start stop)⟩

end DuplicatePrefix.S05NoCutoffClassOwnership
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S05NoCutoffClassOwnership.authorization,
      ``DuplicatePrefix.S05NoCutoffClassOwnership.row,
      ``DuplicatePrefix.S05NoCutoffClassOwnership.positive] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
