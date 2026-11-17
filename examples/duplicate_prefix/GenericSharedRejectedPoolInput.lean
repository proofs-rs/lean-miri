import duplicate_prefix.GenericSharedRejectedInput
import duplicate_prefix.GeneralBorrowFreshSharedNextPool
namespace DuplicatePrefix.GenericSharedRejectedPoolInput
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows
set_option autoImplicit false in
/-- Initial PC2:11 data for an arbitrary coherent free pool. No intermediate
borrow contract, cleanup Plan or successful operation is assumed. -/
structure Input extends GenericSharedRejectedInput.Base where
  pool : GeneralBorrowFreshAllocatorInvariant.Pool entry.allocation.extra.nodes entry.allocation.extra.tagMapping.deassigned
  accounting : GeneralBorrowFreshStagePool.Accounting entry.allocation.extra
  cleanVacant : ∀ query, entry.allocation.extra.nodes.get query = none →
    GeneralBorrowFreshFutureClean.Clean entry.allocation.extra query
  nodeRoom : entry.allocation.extra.nodes.size+3 ≤ 4294967295

instance : Coe Input GenericSharedRejectedInput.Base := ⟨Input.toBase⟩
end DuplicatePrefix.GenericSharedRejectedPoolInput
