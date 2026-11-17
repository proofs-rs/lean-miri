import duplicate_prefix.CurrentCallPostEntryCheckpoint
import duplicate_prefix.CurrentCallEmptyContinuation
namespace DuplicatePrefix.CurrentCallEmptyReturnCore
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open CandidateCurrentJointCall
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- The source-neutral actual Bool producer feeds the same optional-ledger
empty continuation for both live and materialized destinations. -/
def of_return {options remaining span place machine tracker}
    (target : CurrentCallPostEntryCheckpoint.Return machine tracker place)
    (source : Option (AllocId×BorTag))
    (ledger : CurrentCallEmptyLedgerRelease.SourceLedger machine target.window.allocation.extra source)
    (frame : FrameState)
    (tags : frame.protectedTags=CurrentCallEmptyLedgerRelease.rows source target.id target.node.tag)
    (model : DuplicatePrefixCallModel.Model options remaining span machine)
    (tracked : machine.borrowTracker=some tracker)
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread?=some thread) :
    CurrentCallEmptyContinuation.Core options remaining span place machine tracker target.data target.owner
      target.id target.offset target.original target.window target.physical := by
  have concrete : ∃id tag,target.window.pointer.value.provenance=.concrete id tag := by
    obtain ⟨node,nodeAt,_,binding⟩:=target.window.binding
    have equal : node=target.node:=Option.some.inj (nodeAt.symm.trans target.nodeAt)
    subst node
    cases provenance : target.window.pointer.value.provenance with
    | concrete id tag=>exact ⟨id,tag,rfl⟩
    | wildcard=>simp only [provenance] at binding;rw [target.hidden] at binding;cases binding
  exact {
    originalId:=target.originalId
    binding:=by simpa only [target.physicalId,target.physicalOffset] using target.binding
    idEq:=target.physicalId
    offsetEq:=target.physicalOffset
    pointerEq:=target.originalPointer.symm
    allocationEq:=target.physicalAllocation
    parentIssued:=target.originalIssued
    parentBinding:=target.originalBinding
    runtime:=target.runtime
    roots:=target.distinct
    short:=target.short
    concrete:=concrete
    node:=target.node
    nodeAt:=target.nodeAt
    hidden:=target.hidden
    active:=target.activity
    source:=source
    ledger:=ledger
    borrowFrame:=frame
    tags:=tags
    edge:=target.edge
    model:=model
    tracked:=tracked
    thread:=thread
    activeThread:=active
    physicalReady:=by simpa only [target.physicalId,target.physicalOffset] using target.profile}
end
end DuplicatePrefix.CurrentCallEmptyReturnCore
