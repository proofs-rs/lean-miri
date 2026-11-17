import duplicate_prefix.S03EmptySharedRuntime

namespace DuplicatePrefix.S03EmptyNextLenInput
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Derive the next len FnEntry allocator packet from the original runtime and
the actual first Shared constructor. No post-operation capability is assumed. -/
noncomputable def form (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag : BorTag) (input : EmptyForestSharedPool.Input tree parentTag global.nextPointerTag)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (room : tree.nodes.size+2 ≤ 4294967295) :
    EmptyForestSharedPool.Input input.after global.nextPointerTag (TypedRetagEmpty.successorTag global.nextPointerTag fresh) := by
  have successor := GenericFunctionEntryNumerics.successor_value global.nextPointerTag fresh
  have nextFresh : GeneralBorrowTagMap.Fresh tree.tagMapping (TypedRetagEmpty.successorTag global.nextPointerTag fresh) := by
    intro row member equal
    have old := runtime.below.mapping row member
    have values := congrArg (fun tag : BorTag => tag.value.toNat) equal
    omega
  have different : global.nextPointerTag ≠ TypedRetagEmpty.successorTag global.nextPointerTag fresh := by
    intro equal
    have values := congrArg (fun tag : BorTag => tag.value.toNat) equal
    omega
  exact EmptyForestSharedPoolNext.next input _ runtime.formed.allocator.pool runtime.formed.allocator.accounting
    (DuplicatePrefixBorrowContract.vacant_clean runtime) nextFresh different (by omega)

end DuplicatePrefix.S03EmptyNextLenInput
