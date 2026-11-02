import duplicate_prefix.GeneralBorrowExposedScopedSharedLeafRun
namespace DuplicatePrefix.GeneralBorrowExposedScopedSharedLeafExpressionData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowFreshMetadataChildShared
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedSharedLeafConstructor (Resources)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Initial leaf resources derive the exact scoped Read data required by the
physical MIR shared-expression statement. No completed access is a premise. -/
theorem build (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : Resources input protections selected head tail writable) :
    ∃ context : GeneralBorrowExposedKnownRootRangeData.Context input.tree input.parent selected head tail,
      GeneralRangeMapOrigins.OwnedOn
        (fun location => Nonempty (GeneralBorrowExposedScopedMixedRangeData.Data input.tree location protections
          input.parent selected head tail raw.component.support writable))
        input.offset (input.offset+input.len) input.tree.locations := by
  let context : GeneralBorrowExposedKnownRootRangeData.Context input.tree input.parent selected head tail := {
    anchorNode := input.parentNode
    selectedNode := raw.selectedNode
    anchorPresent := input.parentPresent
    selectedPresent := raw.selectedPresent
    roots := raw.roots
    depth := input.depth
    children := input.children
    tags := raw.tags }
  have short : input.tree.nodes.size < 65536 := by have bound := raw.room;omega
  have owned : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowExposedScopedMixedRangeData.Data input.tree location protections
        input.parent selected head tail raw.component.support writable)) input.offset (input.offset+input.len) input.tree.locations := by
    intro position valid positive lower upper
    let location := (input.tree.locations.entries[position]'valid).data
    have mixed := raw.owned position valid positive lower upper
    have leaves : ∀ query,area.support query → ∃ node,input.tree.nodes.get query = some node ∧ node.children = #[] ∧ node.isExposed = true ∧
        GeneralBorrowExposureCardinality.supports (GeneralBorrowExposureCardinality.effective location protections query node) .Read = true ∧
        (GeneralBorrowWildcardVirtualLeaf.effective location query node).possible = true := by
      intro query included
      obtain ⟨node,present,leaf,exposed⟩ := raw.leaves query included
      have stored := raw.unique query included position valid
      change location.perms.get query = some GeneralBorrowWildcardLeaf.unique at stored
      refine ⟨node,present,leaf,exposed,?_,?_⟩
      · simp [GeneralBorrowExposureCardinality.effective,stored,GeneralBorrowWildcardLeaf.unique,Permission.strongestAllowedLocalAccess,
          GeneralBorrowExposureCardinality.supports,GeneralBorrowExposureAncestorFold.supportsRead]
      · simp [GeneralBorrowWildcardVirtualLeaf.effective,stored,GeneralBorrowWildcardLeaf.unique,LocationState.possible]
    exact ⟨GeneralBorrowExposedScopedLeafSeed.seed input.tree location protections input.parent selected head tail raw.component.support writable
      context raw.forest raw.component rfl mixed raw.rootPath raw.hidden raw.separate (raw.coherent position valid) short leaves raw.first raw.rest⟩
  exact ⟨context,owned⟩
end DuplicatePrefix.GeneralBorrowExposedScopedSharedLeafExpressionData
