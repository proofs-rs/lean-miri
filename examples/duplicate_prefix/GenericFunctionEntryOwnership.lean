import duplicate_prefix.GenericFunctionEntryArguments
import duplicate_prefix.GeneralBorrowFreshMutableStages

namespace DuplicatePrefix.GenericFunctionEntryOwnership
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree

set_option autoImplicit false in
/-- The actual generic ROOT argument child retains mutable ownership and confines
its active permissions to the input slice. Cleanliness is required only of the
initial allocator slot; no poststate certificate or operation success is assumed. -/
theorem child
    (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GenericAsMutPtrEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree =>
      location.perms.get (GeneralBorrowFreshMutableStages.slot_index data.slot) = none) tree.locations) :
    let finalTree := GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len
    let index := GeneralBorrowFreshMutableStages.slot_index data.slot
    let protections := (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags
    GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned finalTree protections index .Write)
      offset (offset+len) finalTree.locations ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin finalTree index .Write offset (offset+len) := by
  exact (GeneralBorrowFreshMutableStages.borrow tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag
    data.parent data.root data.node data.depth data.children data.parentPresent data.roots data.covered
    data.tagPresent data.tagFresh data.protectorFresh data.nodeFits data.slot offset len nonzero data.well bounds data.owned clean).2.2

end DuplicatePrefix.GenericFunctionEntryOwnership
