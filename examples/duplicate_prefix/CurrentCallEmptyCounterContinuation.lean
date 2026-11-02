import duplicate_prefix.CurrentCallEmptyContinuation
import duplicate_prefix.CurrentCallEmptyIntegerCounterFrame
namespace DuplicatePrefix.CurrentCallEmptyContinuation
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
/-- Actual source-tree-skipping helpers restore the complete protector table.
Their two fresh tags are relative to the CURRENT entry tracker; conversion
before entry may already have allocated other tags. -/
theorem Core.counter_view {options remaining span place machine tracker data owner id offset original B physical}
    (core : Core options remaining span place machine tracker data owner id offset original B physical)
    (post : Before) (nextTracker : MachineHooks.BorrowState)
    (memory : post.memory=machine.memory) (addresses : post.user.addresses=machine.user.addresses)
    (extras : post.user.payload.payload.user.runtime.extras=machine.user.payload.payload.user.runtime.extras)
    (global : nextTracker.global={tracker.global with nextPointerTag:=nextTracker.global.nextPointerTag})
    (monotone : tracker.global.nextPointerTag.value.toNat≤nextTracker.global.nextPointerTag.value.toNat)
    (model : DuplicatePrefixCallModel.Model options remaining span post) (tracked : post.borrowTracker=some nextTracker)
    (thread : Miri.Concurrency.ThreadRecord) (active : post.threads.activeThread?=some thread) :
    ∃Q : UniformWindow post nextTracker data owner id offset 1 .ret,∃P : CurrentCallBoolScalarWrite.Window post place,
      ∃after : Core options remaining span place post nextTracker data owner id offset original Q P,
        after.source=core.source ∧after.borrowFrame=core.borrowFrame ∧after.node=core.node := by
  obtain ⟨Q,pointer,allocation,precise,runtime⟩:=CurrentCallEmptyIntegerCounterFrame.window B core.runtime post nextTracker memory global monotone
  obtain ⟨P,pointerEq,idEq,offsetEq,entryEq,binding⟩:=CurrentCallRootPhysicalWindow.view (final:=post) physical core.binding addresses (congrArg MemoryState.live memory)
  have present : Present (ActualWorld post) id B.allocation := by unfold Present ActualWorld;rw [memory];exact B.present
  have parent:=CurrentCallAllocationLicense.spatial core.parentIssued post nextTracker B.allocation present
    (by rw [global];rfl) rfl rfl rfl (by intro position root found;exact found)
    (by intro index node found;exact ⟨node,found,rfl,rfl,rfl,rfl⟩)
    B.precise.completion (by intro first second edge;exact edge)
  let after : Core options remaining span place post nextTracker data owner id offset original Q P:={
    originalId:=core.originalId,binding:=binding,idEq:=idEq.trans core.idEq,offsetEq:=(congrArg UInt64.toNat offsetEq).trans core.offsetEq,
    pointerEq:=pointerEq.trans core.pointerEq,allocationEq:=by rw [allocation];exact (congrArg LocalAllocation.allocation entryEq).trans core.allocationEq,
    parentIssued:=by rw [allocation,precise];exact parent,
    parentBinding:=by rw [allocation];exact core.parentBinding,runtime:=runtime,
    roots:=by rw [allocation];exact core.roots,short:=by rw [allocation];exact core.short,
    concrete:=by rw [pointer];exact core.concrete,node:=core.node,
    nodeAt:=by rw [allocation,pointer];exact core.nodeAt,hidden:=core.hidden,
    active:=by rw [allocation,pointer,offsetEq];exact core.active,
    source:=core.source,ledger:=by rw [allocation];exact core.ledger.transport memory,
    borrowFrame:=core.borrowFrame,tags:=core.tags,edge:=by rw [precise,pointer];exact core.edge,
    model:=model,tracked:=tracked,thread:=thread,activeThread:=active,
    physicalReady:=by rw [idEq,offsetEq];exact core.physicalReady.transport extras}
  exact ⟨Q,P,after,rfl,rfl,rfl⟩
end
end DuplicatePrefix.CurrentCallEmptyContinuation
