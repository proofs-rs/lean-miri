import duplicate_prefix.GeneralBorrowExposedScopedInactiveWindowWritableSharedConstructor
import duplicate_prefix.GeneralBorrowExposedScopedInactiveLeafSeed
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWindowWritableSharedData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowFreshMetadataChildShared
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedInactiveWindowWritableSharedConstructor (Resources)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Initial leaf resources derive the exact scoped Read data required by the
physical MIR shared-expression statement. No completed access is a premise. -/
theorem build (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : Resources input protections selected head tail writable) :
    ∃ context : GeneralBorrowExposedKnownRootRangeData.Context input.tree input.parent selected head tail,
      GeneralRangeMapOrigins.OwnedOn
        (fun location => Nonempty (GeneralBorrowExposedScopedInactiveWritableReadData.Data input.tree location protections
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
      (fun location => Nonempty (GeneralBorrowExposedScopedInactiveWritableReadData.Data input.tree location protections
        input.parent selected head tail raw.component.support writable)) input.offset (input.offset+input.len) input.tree.locations := by
    intro position valid positive lower upper
    let location := (input.tree.locations.entries[position]'valid).data
    have mixed := raw.owned position valid positive lower upper
    have leaves : ∀ query,area.support query → ∃ node,input.tree.nodes.get query = some node ∧ node.children = #[] ∧ node.isExposed = true ∧
        GeneralBorrowExposureCardinality.supports (GeneralBorrowExposureCardinality.effective location protections query node) .Read = true ∧
        (GeneralBorrowWildcardVirtualLeaf.effective location query node).possible = true := by
      intro query included
      obtain ⟨node,present,leaf,exposed⟩ := raw.leaves query included
      have compatible:=raw.writableLeaves position valid query node included present
      exact ⟨node,present,leaf,exposed,GeneralBorrowSparseExposedLeafState.supports _ _ compatible .Read,compatible.1⟩
    have ancestors : ∀ query node state,raw.component.support query.toNat → input.tree.nodeAt query=some node → node.isExposed=true →
        input.tree.locationStateAt location query=some state →
        (query.toNat ∈ (source_normal_projection input.tree location protections).topology.ancestorPath input.parent.toNat ∧ state.permission=.Unique) ∨
        (query.toNat ∉ (source_normal_projection input.tree location protections).topology.ancestorPath input.parent.toNat ∧ state.permission=.Disabled) := by
      intro query node state member present exposed statePresent
      have stateEq : ((location.perms.get query).getD node.defaultLocationState)=state := by
        simpa only [BorrowTree.locationStateAt,present,bind,pure,Option.bind_some,Option.some.injEq] using statePresent
      have current:=raw.exposures position valid positive lower upper query node member present exposed
      rw [stateEq] at current
      exact current
    let inactive:=GeneralBorrowExposedScopedInactiveLeafSeed.seed input.tree location protections input.parent selected head tail raw.component.support writable
      context raw.forest raw.component rfl mixed raw.rootPath ancestors raw.separate (raw.coherent position valid) short leaves raw.first raw.rest
    let base : GeneralBorrowExposedScopedInactiveMixedRangeData.Data input.tree location protections input.parent selected head tail raw.component.support writable :=
      ⟨inactive,rfl,mixed⟩
    exact ⟨⟨base,short,raw.leaves,raw.writableLeaves position valid⟩⟩
  exact ⟨context,owned⟩
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWindowWritableSharedData
