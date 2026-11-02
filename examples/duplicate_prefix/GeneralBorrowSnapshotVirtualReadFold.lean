import duplicate_prefix.GeneralBorrowSnapshotReadOtherRoot
import duplicate_prefix.GeneralBorrowWildcardVirtualLeafFold
namespace DuplicatePrefix.GeneralBorrowSnapshotVirtualReadFold
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization
open GeneralBorrowWildcardPrimaryReadWitness (PointwiseReadFrame)
open GeneralBorrowExposedNonleafState (ReadFrame)
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- Static physical-root support data, independent of the current row. -/
structure RootData (tree : BorrowTree) (root : UniIndex) (support : UniIndex → Prop) where
  rooted : support root
  present : ∀ index, support index → ∃ node, tree.nodes.get index = some node
  children : ∀ index node, support index → tree.nodes.get index = some node →
    ∀ child ∈ node.children.toList, support child
  covers : ∀ index, support index → GeneralBorrowExposureCardinality.Covers tree.nodes root index
  member : root ∈ tree.roots.toList

def RootData.control {tree root support} (data : RootData tree root support) : GeneralBorrowWildcardControlStack.Support tree root :=
  ⟨support,data.rooted,data.present,data.children⟩

def SnapshotFamily (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (maximum : Option BorTag) (roots : List UniIndex) (support : UniIndex → UniIndex → Prop) : Prop :=
  ∀ root ∈ roots, Snapshot tree location protections root 1 maximum .Read (support root)

/-- Every nonzero physical position has exactly the same virtual callback
classification and no primary supporting-witness obligation. -/
theorem normalize_virtual (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (virtual : position ≠ 0) (snapshot : Snapshot tree location protections root position maximum .Read support) :
    Snapshot tree location protections root 1 maximum .Read support := by
  refine ⟨?_,?_⟩
  · intro index node included present
    simpa only [relation,show (position != 0) = true by simp [virtual],show (1 != 0) = true from rfl]
      using snapshot.scalar index node included present
  · intro impossible
    cases impossible

/-- The actual finite virtual-root callback fold, in source order. Each
callback derives its real DFS completion; other-root snapshots are transported
using physical-root separation and real counter/outside frames. -/
theorem run (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (roots : List UniIndex) (maximum : Option BorTag) (support : UniIndex → UniIndex → Prop)
    (distinct : roots.Nodup) (data : ∀ root ∈ roots, RootData tree root (support root))
    (snapshots : SnapshotFamily tree initial protections maximum roots support)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := GeneralBorrowWildcardVirtualLeafFold.run tree roots initial maximum .Read protections
    result.status = .Completed ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    ReadFrame initial result.location ∧ PointwiseReadFrame tree protections initial result.location ∧
    (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) ∧
    (∀ query, (∀ root ∈ roots, ¬ support root query) → result.location.perms.get query = initial.perms.get query) := by
  induction roots generalizing initial with
  | nil => exact ⟨rfl,coherent,profile,possible,(fun _ => rfl),(fun _ _ _ => rfl),(fun _ _ => rfl),(fun _ _ => rfl)⟩
  | cons root rest ih =>
    have headData := data root (by simp)
    obtain ⟨depth⟩ := formed.depth
    obtain ⟨forest⟩ := formed.forest initial protections
    obtain ⟨headStatus,headCounters,headSnapshot,headPointwise,headCoherent,headOutside,headProfile,headPossible,headAbsent⟩ :=
      GeneralBorrowSnapshotVirtualReadAccess.access_runtime tree initial protections root 1 maximum (by decide)
        headData.control (snapshots root (by simp)) depth forest coherent profile possible
    have nextSnapshots : SnapshotFamily tree
        (tree.performWildcardAccessAt initial root maximum .Read protections true).location protections maximum rest support := by
      intro other member
      have otherData := data other (by simp [member])
      have different : root ≠ other := by
        intro same
        subst other
        exact (List.nodup_cons.mp distinct).1 member
      exact GeneralBorrowSnapshotReadTransport.transport_other tree initial _ protections formed root other
        headData.member otherData.member different (support root) (support other) headData.covers otherData.present otherData.covers
        1 maximum (snapshots other (by simp [member])) headCounters headOutside
    have tail := ih (tree.performWildcardAccessAt initial root maximum .Read protections true).location
      (List.nodup_cons.mp distinct).2 (by intro other member;exact data other (by simp [member])) nextSnapshots headCoherent headProfile headPossible
    simp only [GeneralBorrowWildcardVirtualLeafFold.run,headStatus,beq_self_eq_true,ite_true]
    refine ⟨tail.1,tail.2.1,tail.2.2.1,tail.2.2.2.1,?_,?_,?_,?_⟩
    · intro query
      exact (tail.2.2.2.2.1 query).trans (headCounters query)
    · intro query node present
      exact (tail.2.2.2.2.2.1 query node present).trans (headPointwise query node present)
    · intro query missing
      exact (tail.2.2.2.2.2.2.1 query missing).trans (headAbsent query missing)
    · intro query outside
      exact (tail.2.2.2.2.2.2.2 query (by intro other member;exact outside other (by simp [member]))).trans
        (headOutside query (outside root (by simp)))

/-- S01 raw residual authorizations initialize all fold snapshots. Positions
are normalized only after their nonzero physical-position facts are supplied. -/
theorem of_authorization (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (roots : List UniIndex) (maximum : Option BorTag) (support : UniIndex → UniIndex → Prop) (positions : UniIndex → Nat)
    (distinct : roots.Nodup) (members : ∀ root ∈ roots, root ∈ tree.roots.toList)
    (virtual : ∀ root ∈ roots, positions root ≠ 0)
    (authorizations : ∀ root ∈ roots, DuplicatePrefixResidualSupportAuthorization.Authorization tree initial protections root (positions root) maximum .Read (support root))
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections) (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := GeneralBorrowWildcardVirtualLeafFold.run tree roots initial maximum .Read protections
    result.status = .Completed ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    ReadFrame initial result.location ∧ PointwiseReadFrame tree protections initial result.location ∧
    (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) ∧
    (∀ query, (∀ root ∈ roots, ¬ support root query) → result.location.perms.get query = initial.perms.get query) := by
  apply run tree initial protections formed roots maximum support distinct
  · intro root member
    have auth := authorizations root member
    exact ⟨auth.rooted,auth.present,auth.children,auth.covers,members root member⟩
  · intro root member
    exact normalize_virtual tree initial protections root (positions root) maximum (support root) (virtual root member)
      (DuplicatePrefixResidualInitialSnapshot.snapshot tree initial protections root (positions root) maximum .Read (support root)
        (authorizations root member) coherent short)
  · exact coherent
  · exact profile
  · exact possible

end DuplicatePrefix.GeneralBorrowSnapshotVirtualReadFold
