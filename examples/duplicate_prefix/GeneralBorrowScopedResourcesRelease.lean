import duplicate_prefix.GeneralBorrowScopedResourcesData
import duplicate_prefix.GeneralBorrowExposedScopedRelease
namespace DuplicatePrefix.GeneralBorrowScopedResourcesRelease
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowFreshMetadataChildShared (Input)
open GeneralBorrowExposedScopedSharedLeafConstructor (Resources)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- A current initial scoped component's Read or Write release is discharged
from raw Resources, activity and stored associated-access policy. The access
kind alignment describes initial permission states; no callback success or
result-state profile is supplied. -/
theorem release (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (kind : AccessKind) (raw : Resources input protections selected head tail (fun _=>true))
    (positive : input.offset.toNat<(input.offset+input.len).toNat)
    (active : GeneralBorrowFreshReleaseLoop.ActiveOn input.tree input.parent kind input.offset (input.offset+input.len))
    (matching : ∀ position (valid : position<input.tree.locations.entries.size) state,
      input.tree.locations.entries[position].data.perms.get input.parent=some state → state.accessed=true →
      ∀ associated,state.permission.associatedAccess=some associated → associated=kind) :
    (input.tree.releaseProtector input.parentTag protections).status=.Released ∧
      (input.tree.releaseProtector input.parentTag protections).tree=
        {input.tree with locations:=(input.tree.releaseProtector input.parentTag protections).tree.locations} := by
  have owned : GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty (GeneralBorrowExposedKnownRootRangeData.Data
      input.tree location protections input.parent selected head tail kind)) input.offset (input.offset+input.len) input.tree.locations := by
    cases kind with
    | Read => exact GeneralBorrowScopedResourcesData.read input protections selected head tail (fun _=>true) raw
    | Write => exact GeneralBorrowScopedResourcesData.write input protections selected head tail raw
  exact GeneralBorrowExposedScopedRelease.release input.tree protections input.parentTag input.parent selected head tail
    (GeneralBorrowScopedResourcesData.context input protections selected head tail (fun _=>true) raw) kind input.offset (input.offset+input.len) positive
    (by have bound:=raw.room;change input.tree.nodes.size≤4294967296;omega)
    (raw.hidden input.parent input.parentNode raw.component.anchor input.parentPresent) input.parentTagPresent active matching owned
end DuplicatePrefix.GeneralBorrowScopedResourcesRelease
