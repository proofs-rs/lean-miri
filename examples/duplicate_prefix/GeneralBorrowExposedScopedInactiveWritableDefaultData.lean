import duplicate_prefix.GeneralBorrowExposedScopedInactiveWindowWritableDefaultData
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableDefaultConstructor
import duplicate_prefix.GeneralBorrowExposedScopedInactiveLeafSeed
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableDefaultData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowFreshMetadataChildDefault
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedInactiveWritableDefaultConstructor (Resources ResourcesFor)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Initial leaf resources derive the exact scoped Read data required by the
physical MIR shared-expression statement. No completed access is a premise. -/
theorem build {profileMode : ProfileMode} (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (raw : ResourcesFor input protections selected head tail profileMode) :
    ∃ context : GeneralBorrowExposedKnownRootRangeData.Context input.tree input.parent selected head tail,
      GeneralRangeMapOrigins.OwnedOn
        (fun location => Nonempty (GeneralBorrowExposedScopedInactiveWritableReadData.Data input.tree location protections
          input.parent selected head tail raw.component.support (fun _=>true)))
        input.offset (input.offset+input.len) input.tree.locations := by
  exact GeneralBorrowExposedScopedInactiveWindowWritableDefaultData.build
    input protections selected head tail
    (GeneralBorrowExposedScopedInactiveWritableDefaultConstructor.ResourcesFor.toWindow input protections selected head tail raw)

end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableDefaultData
