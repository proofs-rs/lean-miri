import duplicate_prefix.GeneralBorrowFreshRootScopedConstructorRange

namespace DuplicatePrefix.GeneralBorrowFreshRootScopedSifa
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowSifa GeneralBorrowView GeneralRangeMapOrigins GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowSharedCallbacksData GeneralBorrowFreshRootScopedAttach
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

def Callbacks (tree : BorrowTree) (protections : ProtectedTags) (selected : UniIndex)
    (maximum : BorTag) (location : LocationTree) : Prop :=
  GeneralBorrowFreshRootSupportCutoff.ExposedBound tree maximum ∧
  ∀ position,(valid : position < tree.roots.size) → selected ≠ tree.roots[position] →
    ∃ support,GeneralBorrowFreshRootSupportCutoff.SupportBound tree maximum support ∧
      DuplicatePrefixResidualSupportAuthorization.Authorization tree location protections tree.roots[position] position (some maximum) .Read support ∧
      DuplicatePrefixResidualSupportAuthorization.Authorization tree location protections tree.roots[position] position (some maximum) .Write support

/-- The actual SIFA loop transports the full callback family on the same
physical owner window; the paired kinds retain one common support. -/
theorem owned (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (parent : UniIndex) (parentNode : TreeNode) (present : tree.nodes.get parent = some parentNode)
    (strongest : IdempotentForeignAccess) (protections : ProtectedTags) (selected : UniIndex) (maximum : BorTag)
    (lower upper : UInt64)
    (initial : OwnedOn (Framed tree protections parent selected maximum) lower upper tree.locations) :
    let after := (sourceUpdateSifa tree parent strongest).1
    OwnedOn (Callbacks after protections selected maximum) lower upper after.locations := by
  dsimp only
  let after := (sourceUpdateSifa tree parent strongest).1
  have shape : treeShape after = treeShape tree := GeneralBorrowSifaView.preserves tree parent strongest
  have roots : after.roots = tree.roots := congrArg (fun value => value.2.2.2) shape
  have ranges := congrArg (fun value => value.2.2.1) shape
  change after.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
    tree.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) at ranges
  have lengths := congrArg Array.size ranges
  simp only [Array.size_map] at lengths
  change OwnedOn (Callbacks after protections selected maximum) lower upper after.locations
  intro position valid positive start stop
  have oldValid : position < tree.locations.entries.size := by omega
  have rangeEq : (after.locations.entries[position]'valid).range = (tree.locations.entries[position]'oldValid).range := by
    have known := congrArg (fun rows => rows[position]?) ranges
    simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,
      Array.getElem?_eq_getElem oldValid,Option.map_some] at known
    exact congrArg Prod.fst (Option.some.inj known)
  change (after.locations.entries[position]'valid).range.start.toNat < upper.toNat at start
  change lower.toNat < (after.locations.entries[position]'valid).range.stop.toNat at stop
  rw [rangeEq] at start stop
  have original := initial position oldValid positive start stop
  refine ⟨GeneralBorrowFreshRootScopedBounds.exposed_sifa tree parent strongest maximum original.1,?_⟩
  intro rootPosition rootValid different
  have oldRootValid : rootPosition < tree.roots.size := by rw [←roots];exact rootValid
  have oldDifferent : selected ≠ tree.roots[rootPosition] := by simpa only [roots] using different
  obtain ⟨support,bounded,read,write,outside⟩ := original.2 rootPosition oldRootValid oldDifferent
  have paths : ∀ query,support query → ¬Path tree query parent := by
    intro query included path
    exact outside query included (path.walk depth)
  obtain ⟨nextReadValid,nextRead⟩ := GeneralBorrowSharedAuthorizationSifaDepth.at_row tree depth parent parentNode present
    strongest protections position oldValid _ rootPosition (some maximum) .Read support read paths
  obtain ⟨nextWriteValid,nextWrite⟩ := GeneralBorrowSharedAuthorizationSifaDepth.at_row tree depth parent parentNode present
    strongest protections position oldValid _ rootPosition (some maximum) .Write support write paths
  have afterBound := GeneralBorrowFreshRootScopedBounds.support_sifa tree parent strongest maximum support read.present bounded
  refine ⟨support,afterBound,?_,?_⟩
  · simpa only [roots] using nextRead
  · simpa only [roots] using nextWrite

end DuplicatePrefix.GeneralBorrowFreshRootScopedSifa
