import duplicate_prefix.GenericAsMutDefaultToCall
import duplicate_prefix.GeneralRootDefaultNextPool

namespace DuplicatePrefix.GenericAsMutDefaultPoolToCall
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
noncomputable section

set_option autoImplicit false in
/-- Initial PC6:7 data for the expression/FnEntry sequence with arbitrary coherent
free pools. Permission cleanliness of initial vacant slots is a separate contract. -/
structure Input where
  common : GenericAsMutDefaultToCall.DataInput
  pool : GeneralBorrowFreshAllocatorInvariant.Pool common.base.data.start.entry.allocation.extra.nodes
    common.base.data.start.entry.allocation.extra.tagMapping.deassigned
  accounting : GeneralBorrowFreshStagePool.Accounting common.base.data.start.entry.allocation.extra
  room : common.base.data.start.entry.allocation.extra.nodes.size+1 ≤ 4294967295
  cleanVacant : ∀ query, common.base.data.start.entry.allocation.extra.nodes.get query = none →
    GeneralBorrowFreshFutureClean.Clean common.base.data.start.entry.allocation.extra query

/-- Construct the actual following call's input with no post-expression
structural record or operation-success premise. -/
def prepare (input : Input) :
    let s := input.common.base.data.start
    Σ' call : GenericAsMutCallToReturn.Input,
      call.caller = GenericAsMutDefaultCore.frame input.common.base ∧
      call.data.start.machine = GenericAsMutDefaultCore.machine s ∧
      PreparedContracts.actualConfig call.data.start.options () (call.data.start.remaining+1) call.data.start.span =
        PreparedContracts.actualConfig s.options () (s.remaining+1) s.span ∧
      call.data.start.limits = s.limits := by
  let s := input.common.base.data.start
  let first := GenericAsMutDefaultCore.first s
  have active : GeneralBorrowFreshActiveWithin.ActiveWithin s.entry.allocation.extra s.data.parent .Write s.offset (s.offset+s.len) := by
    rw [←input.common.target]
    exact input.common.base.data.targetWithin
  let supplied := GeneralRootDefaultNextPool.build s.entry.allocation.extra s.tracker.global.nextPointerTag
    (ReferenceBorrowDriver.allocatedTracker s.tracker s.fresh).global.nextPointerTag s.data.parent s.tracker.global.protectedTags
    s.offset s.len first.nonzero first first.bounds s.data.owned active input.pool input.accounting input.room
    input.common.mapFresh input.common.nodeFresh input.common.different input.cleanVacant
  exact GenericAsMutDefaultToCall.prepare_data input.common supplied.1 rfl supplied.2.1 supplied.2.2
end
end DuplicatePrefix.GenericAsMutDefaultPoolToCall
