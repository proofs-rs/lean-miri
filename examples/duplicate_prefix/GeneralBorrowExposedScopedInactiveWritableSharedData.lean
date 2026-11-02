import duplicate_prefix.GeneralBorrowExposedScopedInactiveWindowWritableSharedData
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableSharedConstructor
import duplicate_prefix.GeneralBorrowExposedScopedInactiveLeafSeed
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSharedData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowFreshMetadataChildShared
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedInactiveWritableSharedConstructor (Resources ResourcesFor)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Initial leaf resources derive the exact scoped Read data required by the
physical MIR shared-expression statement. No completed access is a premise. -/
theorem build {profileMode : ProfileMode} (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : ResourcesFor input protections selected head tail writable profileMode) :
    ∃ context : GeneralBorrowExposedKnownRootRangeData.Context input.tree input.parent selected head tail,
      GeneralRangeMapOrigins.OwnedOn
        (fun location => Nonempty (GeneralBorrowExposedScopedInactiveWritableReadData.Data input.tree location protections
          input.parent selected head tail raw.component.support writable))
        input.offset (input.offset+input.len) input.tree.locations := by
  exact GeneralBorrowExposedScopedInactiveWindowWritableSharedData.build
    input protections selected head tail writable
    (GeneralBorrowExposedScopedInactiveWritableSharedConstructor.ResourcesFor.toWindow input protections selected head tail writable raw)

end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSharedData
