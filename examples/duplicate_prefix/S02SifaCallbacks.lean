import duplicate_prefix.S02SifaAuthorizationStep

namespace DuplicatePrefix.S02SifaCallbacks
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowSifa GeneralBorrowView GeneralBorrowNodeUpdate DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Exact callback family of a destination Row; supports may vary by row and
physical root, and wildcard destinations retain every root. -/
def Callbacks (tree : BorrowTree) (protections : ProtectedTags) (selected : Option UniIndex)
    (maximum : Option BorTag) (location : LocationTree) : Prop :=
  ∀ position,(valid : position < tree.roots.size) → selected ≠ some tree.roots[position] →
    ∃ support,Authorization tree location protections tree.roots[position] position maximum .Read support ∧
      Authorization tree location protections tree.roots[position] position maximum .Write support

/-- A real single ancestor weakening preserves all destination root callbacks,
including the constructor parent's component when it is a callback root. -/
theorem weakened (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (location : LocationTree) (protections : ProtectedTags) (selected : Option UniIndex) (maximum : Option BorTag)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (old : Callbacks tree protections selected maximum location) :
    Callbacks (GeneralBorrowSifa.weakened tree index node .Read) protections selected maximum
      (weakenLocation location index .Read) := by
  intro position valid different
  obtain ⟨support,read,write⟩ := old position valid different
  exact ⟨support,
    S02SifaAuthorizationStep.weakened tree depth index node present location protections _ position maximum .Read support read
      (fun query value _ found => profile.present query value found),
    S02SifaAuthorizationStep.weakened tree depth index node present location protections _ position maximum .Write support write
      (fun query value _ found => profile.present query value found)⟩

/-- Actual SIFA preserves the complete existential paired callback family on
an arbitrary destination byte window. The constructor source and destination
selected root may differ, or the destination may be wildcard. -/
theorem owned (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (start : UniIndex) (protections : ProtectedTags) (selected : Option UniIndex)
    (maximum : Option BorTag) (lower upper : UInt64)
    (profile : GeneralRangeMapState.Every (fun location => GeneralBorrowLocationSifaConsistency.Profile tree location protections) tree.locations)
    (initial : GeneralRangeMapOrigins.OwnedOn (Callbacks tree protections selected maximum) lower upper tree.locations) :
    let after := (sourceUpdateSifa tree start .Read).1
    GeneralRangeMapOrigins.OwnedOn (Callbacks after protections selected maximum) lower upper after.locations := by
  let P (current : BorrowTree) : Prop :=
    Nonempty (GeneralBorrowExposure.ParentDepth current.nodes) ∧
    GeneralRangeMapState.Every (fun location => GeneralBorrowLocationSifaConsistency.Profile current location protections) current.locations ∧
    GeneralRangeMapOrigins.OwnedOn (Callbacks current protections selected maximum) lower upper current.locations
  have initialized : P tree := ⟨⟨depth⟩,profile,initial⟩
  have maintained := S02SifaAuthorizationStep.loop_invariant P tree start initialized (by
    intro current index node present packet
    obtain ⟨⟨currentDepth⟩,currentProfile,currentOwned⟩ := packet
    have shape := weakened_tree_shape current index node present .Read
    refine ⟨⟨GeneralBorrowFreshMetadata.parent_depth current _ shape currentDepth⟩,
      GeneralBorrowSifaProfileTransport.weakened_profile current protections index node present .Read currentProfile,?_⟩
    intro row valid positive start stop
    have previous : row < current.locations.entries.size := by
      simpa only [GeneralBorrowSifa.weakened,DedupRangeMap.modifyAll,Array.size_map] using valid
    have rowEq : (GeneralBorrowSifa.weakened current index node .Read).locations.entries[row].data =
        weakenLocation current.locations.entries[row].data index .Read := by
      simp only [GeneralBorrowSifa.weakened,DedupRangeMap.modifyAll,Array.getElem_map,weakenLocation]
      rfl
    have rangeEq : (GeneralBorrowSifa.weakened current index node .Read).locations.entries[row].range = current.locations.entries[row].range := by
      simp only [GeneralBorrowSifa.weakened,DedupRangeMap.modifyAll,Array.getElem_map]
    rw [rangeEq] at start stop
    have original := currentOwned row previous positive start stop
    rw [rowEq]
    exact weakened current currentDepth index node present _ protections selected maximum (currentProfile row previous) original)
  exact maintained.2.2

end DuplicatePrefix.S02SifaCallbacks
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02SifaCallbacks.weakened,``DuplicatePrefix.S02SifaCallbacks.owned] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
