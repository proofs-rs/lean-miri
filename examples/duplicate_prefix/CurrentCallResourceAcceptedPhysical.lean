import duplicate_prefix.CurrentCallResourceAcceptedCopy
import duplicate_prefix.CurrentCallResourceLenPhysical
import duplicate_prefix.CurrentCallScalarTreeWindow
import duplicate_prefix.CurrentCallCopyBoolWindow
namespace DuplicatePrefix.CurrentCallResourceAcceptedPhysical
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallResourceEntryBody
open CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
private theorem tick_memory (options remaining span machine) :
    (RootZeroCompleteState.tick options remaining span machine).memory=machine.memory:=by
  unfold RootZeroCompleteState.tick SourceControl.accounted
  rw [(actual_fields options () (remaining+1) span).terminators]
variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    {out : Output limits C count} {ready : CurrentCallResourceBodyReadiness.Ready C} {nextData nextOwner}
    {Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut}
    {stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)}
    {result : CurrentCallResourceLenReturn.Result out ready Q stage}
    (done : CurrentCallResourceAsMutInvoke.DefaultResult result)
    (fresh : done.nextTracker.global.nextPointerTag.value<18446744073709551615)
    (valid15 : (15 : MIR.LocalId)<done.frame.locals.size)
    (seed : CurrentCallResourceAsMutCall.Seed options limits remaining span done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15)
    (returned : CurrentCallResourceAsMutReturn.Returned done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed)

/-- The original destination geometry survives the actual Default/S helper
and release/pop sequence; no original pointer is replaced by the child tag. -/
theorem before_copy : ∃ physical : CurrentCallBoolScalarWrite.Window returned.machine place,
    physical.pointer=C.physical.pointer ∧physical.id=C.physical.id ∧physical.offset=C.physical.offset ∧
    CandidateCallBindings.WindowBinding returned.machine physical.pointer physical.id physical.offset.toNat 1:=by
  obtain ⟨old,pointer,idEq,offsetEq,binding⟩:=CurrentCallResourceLenPhysical.of_return result
  have live:=result.sourceLive
  have sourceAllocation : done.entry.allocation.setExtra (CurrentCallResourceAsMutReturn.releasedTree done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed)=
      (CurrentCallResourceAsMutInvoke.sourceEntry (out:=out) (ready:=ready)).allocation.setExtra
        (CurrentCallResourceAsMutReturn.releasedTree done.current done.entry done.frame done.base
          (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed):=by
    change done.current.allocation.setExtra _=_
    rw [done.allocation,done.qAllocation]
    exact AllocationCopy.set_extra_twice _ _ _
  have beforeMemory : (CurrentCallResourceAsMutInvoke.beforeDefault result).memory=result.machine.memory:=by
    rw [CurrentCallResourceAsMutInvoke.beforeDefault,tick_memory,tick_memory]
  have heap : returned.machine.memory.live=(result.machine.memory.live.filter (fun row=>row.1!=id)).push
      (id,{(CurrentCallResourceAsMutInvoke.sourceEntry (out:=out) (ready:=ready)) with allocation:=(
        (CurrentCallResourceAsMutInvoke.sourceEntry (out:=out) (ready:=ready)).allocation.setExtra
          (CurrentCallResourceAsMutReturn.releasedTree done.current done.entry done.frame done.base
            (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed))}):=by
    have rowEq : {done.entry with allocation:=(done.entry.allocation.setExtra
        (CurrentCallResourceAsMutReturn.releasedTree done.current done.entry done.frame done.base
          (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed))}=
        {(CurrentCallResourceAsMutInvoke.sourceEntry (out:=out) (ready:=ready)) with allocation:=(
          (CurrentCallResourceAsMutInvoke.sourceEntry (out:=out) (ready:=ready)).allocation.setExtra
            (CurrentCallResourceAsMutReturn.releasedTree done.current done.entry done.frame done.base
              (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed))}:=by
      change (⟨_,done.entry.allocation.setExtra _⟩ : LocalAllocation Provenance BorrowTree MiriMemoryKind)=_
      rw [sourceAllocation]
    rw [returned.memory]
    change ((done.machine.memory.live.filter (fun row=>row.1!=id)).push _)=_
    have machineLive:=congrArg (fun machine : Before=>machine.memory.live) done.machineEq
    rw [rowEq,machineLive]
    change (((CurrentCallResourceAsMutInvoke.beforeDefault result).memory.live.filter (fun row=>row.1!=id)).push _ |>.filter (fun row=>row.1!=id)).push _=_
    rw [beforeMemory]
    exact congrArg (fun memory=>memory.live) (MemoryCopyBridge.live_update_twice result.machine.memory id _ _)
  obtain ⟨next,nextPointer,nextId,nextOffset,nextBinding⟩:=CurrentCallScalarTreeWindow.replace old binding id
    (CurrentCallResourceAsMutInvoke.sourceEntry (out:=out) (ready:=ready))
    (CurrentCallResourceAsMutReturn.releasedTree done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed)
    live (CurrentCallResourceAsMutFacts.addresses done fresh valid15 seed returned) heap
  exact ⟨next,nextPointer.trans pointer,nextId.trans idEq,nextOffset.trans offsetEq,nextBinding⟩

/-- Physical copy metadata preserves the SAME original Bool place, including
the same-allocation case and arbitrary supported pointer-byte fragments. -/
theorem current (copied : CurrentCallResourceAcceptedCopy.Result done fresh valid15 seed returned) :
    ∃ physical : CurrentCallBoolScalarWrite.Window copied.machine place,
      physical.pointer=C.physical.pointer ∧physical.id=C.physical.id ∧physical.offset=C.physical.offset ∧
      CandidateCallBindings.WindowBinding copied.machine physical.pointer physical.id physical.offset.toNat 1:=by
  obtain ⟨old,pointer,idEq,offsetEq,binding⟩:=before_copy done fresh valid15 seed returned
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind:=
    {done.entry with allocation:=done.entry.allocation.setExtra (CurrentCallResourceAsMutReturn.releasedTree done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed)}
  have bytes : copied.allocation.byteSize=entry.allocation.byteSize:=by
    change copied.allocation.byteSize=done.entry.allocation.byteSize
    exact copied.byteSize.trans (congrArg Allocation.byteSize seed.allocationEq)
  have length : copied.allocation.len=entry.allocation.len:=by
    change copied.allocation.len=done.entry.allocation.len
    exact copied.length.trans (congrArg Allocation.len seed.allocationEq)
  have heap : copied.machine.memory.live=(returned.machine.memory.live.filter (fun row=>row.1!=id)).push
      (id,{entry with allocation:=copied.allocation}):=by
    rw [copied.memory]
    change ((AddOutput.machine options remaining span returned.machine).memory.live.filter (fun row=>row.1!=id)).push _=_
    rw [(AddOutput.preserved options remaining span returned.machine).1]
  obtain ⟨next,nextPointer,nextId,nextOffset,nextBinding⟩:=CurrentCallCopyBoolWindow.replace old binding id entry copied.allocation returned.sourceLive
    bytes length copied.physical.mutable copied.physical.maskValid copied.physical.maskLength copied.physical.pointerBounds copied.addresses heap
  exact ⟨next,nextPointer.trans pointer,nextId.trans idEq,nextOffset.trans offsetEq,nextBinding⟩
end
end DuplicatePrefix.CurrentCallResourceAcceptedPhysical
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceAcceptedPhysical" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved accepted original destination dependency {dependency}"
