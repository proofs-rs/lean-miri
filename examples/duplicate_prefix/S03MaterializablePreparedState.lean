import duplicate_prefix.S03MaterializableReturnState
import duplicate_prefix.S03MaterializableRootRuntime

namespace DuplicatePrefix.S03MaterializablePreparedState
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Initial return data on the exact prepared machine appearing on the right
of the actual call equality. No tag has been consumed at this stage. -/
def input {options : EvalConfigurationCore.Options} {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place) (id : AllocId) (tag : Option BorTag)
    (packet : S03MaterializableInput.Packet options before original.tracker id tag)
    (converted : Allocation Provenance Unit) :
    DuplicatePrefixReturnPlaceInput.Input
      (GlobalEmptyRootCopy.preparedMachine options before id packet.root packet.source converted) place :=
  S03SeparateEmptyArgument.transport original _ original.tracker original.enabled
    ((GlobalEmptyRootPrepared.live_other options before id original.id packet.root packet.source converted
      (S03MaterializableInput.separate packet original)).trans original.live) rfl original.borrow

/-- The initially absent image's fresh root runtime is derived locally, using
the existing return allocation solely to obtain the global protector bound. -/
theorem argument_runtime {options : EvalConfigurationCore.Options} {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts original.entry.allocation.extra original.tracker.global)
    (id : AllocId) (tag : Option BorTag)
    (packet : S03MaterializableInput.Packet options before original.tracker id tag) :
    DuplicatePrefixBorrowContract.RuntimeFacts (BorrowTree.new packet.root packet.source.byteSize) original.tracker.global :=
  S03MaterializableRootRuntime.initial packet.root packet.source.byteSize.bytes original.tracker.global packet.rootBelow runtime.below.protectors

theorem model {options : EvalConfigurationCore.Options} {remaining : Nat}
    {span : PreparedContracts.FixedSpanQuery} {before : Before}
    (initial : DuplicatePrefixCallModel.Model options remaining span before)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit)
    (converted : Allocation Provenance Unit) (nextRemaining : Nat) :
    DuplicatePrefixCallModel.Model options nextRemaining span
      (GlobalEmptyRootCopy.preparedMachine options before id root source converted) := by
  have shifted := S03IntegerZeroState.retime initial nextRemaining
  have controls : (PreparedContracts.actualConfig options () (nextRemaining+1) span).terminators.getControl
      (GlobalEmptyRootCopy.preparedMachine options before id root source converted).user =
      (PreparedContracts.actualConfig options () (nextRemaining+1) span).terminators.getControl before.user := by
    rw [(CanonicalConfigFacts.actual_fields options () (nextRemaining+1) span).terminators]
    rfl
  refine {shifted with unchecked := ?_,noGc := ?_}
  · rw [controls];exact shifted.unchecked
  · rw [controls];exact shifted.noGc

theorem return_extras {options : EvalConfigurationCore.Options} {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place) (id : AllocId) (tag : Option BorTag)
    (packet : S03MaterializableInput.Packet options before original.tracker id tag)
    (converted : Allocation Provenance Unit) :
    (GlobalEmptyRootCopy.preparedMachine options before id packet.root packet.source converted).user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == original.id) = before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == original.id) :=
  GlobalEmptyRootPrepared.extras_other options before id original.id packet.root packet.source converted
    (S03MaterializableInput.separate packet original)

end
end DuplicatePrefix.S03MaterializablePreparedState
