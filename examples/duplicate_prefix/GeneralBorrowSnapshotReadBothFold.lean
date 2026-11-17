import duplicate_prefix.GeneralBorrowSnapshotAnyKindTransport
import duplicate_prefix.GeneralBorrowSnapshotVirtualReadBothAuthorization
import duplicate_prefix.GeneralBorrowWildcardVirtualLeafFold
namespace DuplicatePrefix.GeneralBorrowSnapshotReadBothFold
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixResidualSupportAuthorization
open GeneralBorrowReadNoMaximumWriteFrame (WriteFrame)
open GeneralBorrowExposedNonleafState (ReadFrame)
open GeneralBorrowWildcardPrimaryReadWitness (PointwiseReadFrame)
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

def BothFamily (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (roots : List UniIndex) (positions : UniIndex → Nat) (support : UniIndex → UniIndex → Prop) : Prop :=
  ∀ root ∈ roots, Authorization tree location protections root (positions root) none .Read (support root) ∧
    Authorization tree location protections root (positions root) none .Write (support root)

/-- A literal no-cutoff virtual Read fold retains BOTH raw callback candidates
for every tracked physical root, including roots processed earlier. Internal
transport uses both global counter frames and real outside-slot framing. -/
theorem run (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (todo tracked : List UniIndex) (positions : UniIndex → Nat) (support : UniIndex → UniIndex → Prop)
    (included : ∀ root ∈ todo, root ∈ tracked) (members : ∀ root ∈ tracked, root ∈ tree.roots.toList)
    (virtual : ∀ root ∈ todo, positions root ≠ 0)
    (family : BothFamily tree initial protections tracked positions support)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections) (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := GeneralBorrowWildcardVirtualLeafFold.run tree todo initial none .Read protections
    result.status = .Completed ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    ReadFrame initial result.location ∧ WriteFrame initial result.location ∧
    PointwiseReadFrame tree protections initial result.location ∧
    (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) ∧
    (∀ query, (∀ root ∈ todo, ¬ support root query) → result.location.perms.get query = initial.perms.get query) ∧
    BothFamily tree result.location protections tracked positions support := by
  induction todo generalizing initial with
  | nil => exact ⟨rfl,coherent,profile,possible,(fun _ => rfl),(fun _ => rfl),(fun _ _ _ => rfl),(fun _ _ => rfl),(fun _ _ => rfl),family⟩
  | cons root rest ih =>
    have rootTracked := included root (by simp)
    have headAuth := family root rootTracked
    obtain ⟨depth⟩ := formed.depth
    obtain ⟨forest⟩ := formed.forest initial protections
    obtain ⟨complete,frame,snapshot,pointwise,afterCoherent,outside,afterProfile,afterPossible,absent,readAfter,writeAfter⟩ :=
      GeneralBorrowSnapshotVirtualReadBothAuthorization.access_both tree initial protections root (positions root) none (support root)
        (virtual root (by simp)) headAuth.1 headAuth.2 depth forest coherent short profile possible
    have writeFrame := GeneralBorrowReadNoMaximumWriteFrame.virtual tree initial protections root (positions root) (virtual root (by simp))
      (support root) headAuth.1 depth forest coherent short profile possible
    have nextFamily : BothFamily tree
        (tree.performWildcardAccessAt initial root none .Read protections true).location protections tracked positions support := by
      intro other member
      by_cases same : other = root
      · subst other
        exact ⟨readAfter,writeAfter⟩
      · have auth := family other member
        have transport (kind : AccessKind) (authorization : Authorization tree initial protections other (positions other) none kind (support other))
            (counterFrame : GeneralBorrowSnapshotAnyKindTransport.CounterFrame initial
              (tree.performWildcardAccessAt initial root none .Read protections true).location kind) :
            Authorization tree (tree.performWildcardAccessAt initial root none .Read protections true).location protections other (positions other) none kind (support other) :=
          GeneralBorrowSnapshotAnyKindTransport.authorization_other tree initial _ protections formed root other
            (members root rootTracked) (members other member) (Ne.symm same) (support root) (support other) headAuth.1.covers
            (positions other) kind authorization coherent afterCoherent short counterFrame outside
        exact ⟨transport .Read auth.1 frame,transport .Write auth.2 writeFrame⟩
    have tail := ih (tree.performWildcardAccessAt initial root none .Read protections true).location
      (by intro other member;exact included other (by simp [member]))
      (by intro other member;exact virtual other (by simp [member])) nextFamily afterCoherent afterProfile afterPossible
    simp only [GeneralBorrowWildcardVirtualLeafFold.run,complete,beq_self_eq_true,ite_true]
    refine ⟨tail.1,tail.2.1,tail.2.2.1,tail.2.2.2.1,?_,?_,?_,?_,?_,tail.2.2.2.2.2.2.2.2.2⟩
    · intro query;exact (tail.2.2.2.2.1 query).trans (frame query)
    · intro query;exact (tail.2.2.2.2.2.1 query).trans (writeFrame query)
    · intro query node present;exact (tail.2.2.2.2.2.2.1 query node present).trans (pointwise query node present)
    · intro query missing;exact (tail.2.2.2.2.2.2.2.1 query missing).trans (absent query missing)
    · intro query excluded
      exact (tail.2.2.2.2.2.2.2.2.1 query (by intro other member;exact excluded other (by simp [member]))).trans
        (outside query (excluded root (by simp)))

end DuplicatePrefix.GeneralBorrowSnapshotReadBothFold
