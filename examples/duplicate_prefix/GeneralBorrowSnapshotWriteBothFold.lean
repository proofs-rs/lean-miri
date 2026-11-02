import duplicate_prefix.GeneralBorrowSnapshotReadBothFold
import duplicate_prefix.DuplicatePrefixVirtualWriteBothClosure
import duplicate_prefix.GeneralBorrowResidualVirtualWriteRuntime
import duplicate_prefix.GeneralBorrowRootLocalCounterFrame
namespace DuplicatePrefix.GeneralBorrowSnapshotWriteBothFold
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
abbrev BothFamily := GeneralBorrowSnapshotReadBothFold.BothFamily

private theorem one (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (virtual : position ≠ 0) (support : UniIndex → Prop)
    (authorization : Authorization tree initial protections root position none .Write support)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections) (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := tree.performWildcardAccessAt initial root none .Write protections true
    result.status = .Completed ∧ GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) ∧
      (∀ query, ¬support query → result.location.perms.get query = initial.perms.get query) ∧
      Authorization tree result.location protections root position none .Read support ∧
      Authorization tree result.location protections root position none .Write support := by
  obtain ⟨done,writeAfter,readAfter,_,_,afterCoherent,outside⟩ :=
    DuplicatePrefixVirtualWriteBothClosure.of_authorization tree initial protections root position none virtual support authorization depth forest coherent short
  obtain ⟨_,removed,_,_,_,_,afterProfile,afterPossible,vacant⟩ :=
    GeneralBorrowResidualVirtualWriteRuntime.of_authorization tree initial protections root position none virtual support authorization depth forest coherent short profile possible
  exact ⟨done,afterCoherent,afterProfile,afterPossible,vacant,outside,readAfter,writeAfter⟩

/-- Literal source-order virtual Write fold preserves BOTH raw authorization
families and runtime invariants. Other roots are transported using only their
own actual counters and physical outside-slot framing; global Read/Write
counter frames are not assumed or claimed. All one-step capabilities are
proved by the concrete actual callback closures above. -/
theorem run (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (todo tracked : List UniIndex) (positions : UniIndex → Nat) (support : UniIndex → UniIndex → Prop)
    (included : ∀ root ∈ todo, root ∈ tracked) (members : ∀ root ∈ tracked, root ∈ tree.roots.toList)
    (virtual : ∀ root ∈ todo, positions root ≠ 0)
    (family : BothFamily tree initial protections tracked positions support)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections) (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := GeneralBorrowWildcardVirtualLeafFold.run tree todo initial none .Write protections
    result.status = .Completed ∧ GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) ∧
      (∀ query, (∀ root ∈ todo, ¬support root query) → result.location.perms.get query = initial.perms.get query) ∧
      BothFamily tree result.location protections tracked positions support := by
  induction todo generalizing initial with
  | nil => exact ⟨rfl,coherent,profile,possible,(fun _ _ => rfl),(fun _ _ => rfl),family⟩
  | cons root rest ih =>
    have rootTracked := included root (by simp)
    have headAuth := family root rootTracked
    obtain ⟨depth⟩ := formed.depth
    obtain ⟨forest⟩ := formed.forest initial protections
    obtain ⟨complete,afterCoherent,afterProfile,afterPossible,vacant,outside,readAfter,writeAfter⟩ :=
      one tree initial protections root (positions root) (virtual root (by simp)) (support root) headAuth.2 depth forest coherent short profile possible
    have nextFamily : BothFamily tree (tree.performWildcardAccessAt initial root none .Write protections true).location protections tracked positions support := by
      intro other member
      by_cases same : other = root
      · subst other
        exact ⟨readAfter,writeAfter⟩
      · have auth := family other member
        have transport (kind : AccessKind) (authorization : Authorization tree initial protections other (positions other) none kind (support other)) :
            Authorization tree (tree.performWildcardAccessAt initial root none .Write protections true).location protections other (positions other) none kind (support other) :=
          GeneralBorrowRootLocalCounterFrame.authorization_other_no_maximum tree initial _ protections formed root other
            (members root rootTracked) (members other member) (Ne.symm same) (support root) (support other) headAuth.2.covers
            (positions other) kind authorization coherent afterCoherent short outside
        exact ⟨transport .Read auth.1,transport .Write auth.2⟩
    have tail := ih (tree.performWildcardAccessAt initial root none .Write protections true).location
      (by intro other member;exact included other (by simp [member]))
      (by intro other member;exact virtual other (by simp [member])) nextFamily afterCoherent afterProfile afterPossible
    simp only [GeneralBorrowWildcardVirtualLeafFold.run,complete,beq_self_eq_true,ite_true]
    obtain ⟨tailDone,tailCoherent,tailProfile,tailPossible,tailVacant,tailOutside,finalFamily⟩ := tail
    refine ⟨tailDone,tailCoherent,tailProfile,tailPossible,?_,?_,finalFamily⟩
    · intro query missing
      exact (tailVacant query missing).trans (vacant query missing)
    · intro query excluded
      exact (tailOutside query (by intro other member;exact excluded other (by simp [member]))).trans (outside query (excluded root (by simp)))
end DuplicatePrefix.GeneralBorrowSnapshotWriteBothFold
