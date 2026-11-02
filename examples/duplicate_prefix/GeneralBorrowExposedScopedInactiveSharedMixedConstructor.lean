import duplicate_prefix.GeneralBorrowExposedScopedInactiveSharedConstructor
import duplicate_prefix.GeneralBorrowExposedScopedInactiveMixedRangeData
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveSharedMixedConstructor
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildShared
open GeneralBorrowExposedScopedInactiveSharedConstructor (Resources)
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Actual shared construction retains both complete exposed-ancestor Read
inputs and the mutable/read-only labels required after the helper returns. -/
theorem construct (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : Resources input protections selected head tail writable) :
    let child := result input
    let support := fun position => raw.component.support position ∨ position=(index input).toNat
    (input.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen input.isProtected).outcome=.ok () ∧
    ∃ context : GeneralBorrowExposedKnownRootRangeData.Context child (index input) selected head tail,
      GeneralRangeMapOrigins.OwnedOn (fun location => Nonempty (GeneralBorrowExposedScopedInactiveMixedRangeData.Data child location protections
        (index input) selected head tail support (GeneralBorrowFreshMixedChild.extend writable (index input).toNat)))
        input.offset (input.offset+input.len) child.locations := by
  obtain ⟨success,context,owned⟩ := GeneralBorrowExposedScopedInactiveSharedConstructor.construct input protections selected head tail writable raw
  have mixed := GeneralBorrowExposedScopedSharedConstructor.append_owned input.tree input.depth input.parentTag input.newTag input.parent input.parentNode
    input.parentTagPresent input.parentPresent input.fresh input.noFree input.aligned input.fits input.isProtected input.offset input.len input.nonzero
    input.well input.bounds protections raw.component.support writable raw.forest raw.owned
  refine ⟨success,context,?_⟩
  intro position valid positive lower upper
  obtain ⟨base⟩ := owned position valid positive lower upper
  exact ⟨{base:=base,support_eq:=base.supportEq,mixed:=mixed.2 position valid positive lower upper}⟩
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveSharedMixedConstructor
