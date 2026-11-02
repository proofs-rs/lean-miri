import duplicate_prefix.GeneralBorrowExposedScopedSharedLeafConstructor
import duplicate_prefix.GeneralBorrowExposedScopedLeafWriteSeed
namespace DuplicatePrefix.GeneralBorrowScopedResourcesData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowFreshMetadataChildShared (Input)
open GeneralBorrowExposedScopedSharedLeafConstructor (Resources)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
noncomputable section

def context (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat→Bool) (raw : Resources input protections selected head tail writable) :
    GeneralBorrowExposedKnownRootRangeData.Context input.tree input.parent selected head tail :=
  ⟨input.parentNode,raw.selectedNode,input.parentPresent,raw.selectedPresent,raw.roots,input.depth,input.children,raw.tags⟩

/-- Initial current-component Resources produce actual scalar Read inputs,
without executing or assuming a constructor or release callback. -/
theorem read (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat→Bool) (raw : Resources input protections selected head tail writable) :
    GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty (GeneralBorrowExposedKnownRootRangeData.Data
      input.tree location protections input.parent selected head tail .Read)) input.offset (input.offset+input.len) input.tree.locations := by
  intro position valid positive lower upper
  let location := (input.tree.locations.entries[position]'valid).data
  have leaves : ∀ query,area.support query → ∃ node,input.tree.nodes.get query=some node ∧ node.children=#[] ∧ node.isExposed=true ∧
      GeneralBorrowExposureCardinality.supports (GeneralBorrowExposureCardinality.effective location protections query node) .Read=true ∧
      (GeneralBorrowWildcardVirtualLeaf.effective location query node).possible=true := by
    intro query included
    obtain ⟨node,present,leaf,exposed⟩ := raw.leaves query included
    have stored := raw.unique query included position valid
    change location.perms.get query=some GeneralBorrowWildcardLeaf.unique at stored
    exact ⟨node,present,leaf,exposed,by simp [GeneralBorrowExposureCardinality.effective,stored,GeneralBorrowWildcardLeaf.unique,
      Permission.strongestAllowedLocalAccess,GeneralBorrowExposureCardinality.supports,GeneralBorrowExposureAncestorFold.supportsRead],
      by simp [GeneralBorrowWildcardVirtualLeaf.effective,stored,GeneralBorrowWildcardLeaf.unique,LocationState.possible]⟩
  exact ⟨(GeneralBorrowExposedScopedLeafSeed.seed input.tree location protections input.parent selected head tail raw.component.support writable
    (context input protections selected head tail writable raw) raw.forest raw.component rfl (raw.owned position valid positive lower upper)
    raw.rootPath raw.hidden raw.separate (raw.coherent position valid) (by have bound:=raw.room;omega) leaves raw.first raw.rest).base⟩

/-- All-writable initial component Resources likewise form the raw Write
callback contract while preserving the exposed other components. -/
theorem write (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (raw : Resources input protections selected head tail (fun _=>true)) :
    GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty (GeneralBorrowExposedKnownRootRangeData.Data
      input.tree location protections input.parent selected head tail .Write)) input.offset (input.offset+input.len) input.tree.locations := by
  intro position valid positive lower upper
  let location := (input.tree.locations.entries[position]'valid).data
  have leaves : ∀ query,area.support query → ∃ node,input.tree.nodes.get query=some node ∧ node.children=#[] ∧ node.isExposed=true ∧
      GeneralBorrowWildcardVirtualLeaf.effective location query node=GeneralBorrowWildcardLeaf.unique := by
    intro query included
    obtain ⟨node,present,leaf,exposed⟩ := raw.leaves query included
    have stored := raw.unique query included position valid
    change location.perms.get query=some GeneralBorrowWildcardLeaf.unique at stored
    exact ⟨node,present,leaf,exposed,by simp [GeneralBorrowWildcardVirtualLeaf.effective,stored]⟩
  exact ⟨GeneralBorrowExposedScopedLeafWriteSeed.seed input.tree location protections input.parent selected head tail raw.component.support
    (context input protections selected head tail (fun _=>true) raw) raw.forest raw.component rfl (raw.owned position valid positive lower upper)
    raw.rootPath raw.hidden raw.separate (raw.coherent position valid) (by have bound:=raw.room;omega) leaves raw.first raw.rest⟩
end
end DuplicatePrefix.GeneralBorrowScopedResourcesData
