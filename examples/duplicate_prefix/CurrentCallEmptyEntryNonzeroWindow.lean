import duplicate_prefix.CurrentCallEmptyEntryNonzeroHeap
import duplicate_prefix.CurrentCallEmptyEntryReturnWindow

namespace DuplicatePrefix.CurrentCallEmptyEntryNonzeroWindow
open Miri Miri.Input Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallEmptyEntryNonzeroDispatch
open CurrentCallEmptyEntryNonzeroDispatchState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section
variable {options limits remaining span before tracker argument place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data}

/-- The real empty-entry mutation and actual two-helper heap retain the
original Bool scalar window. No post-clear full provenance well-formedness or
new caller readiness/operation premise is needed. -/
theorem of_body (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64)
    (facts : CurrentCallEmptyEntryRoot.Facts out count)
    (result : CompilerFrameContext.ActualFrame) (post : Before) (body : BodyResult out count result post) :
    ∃ window : CurrentCallBoolScalarWrite.Window post place,
      window.pointer = out.physical.pointer ∧ window.id = out.physical.id ∧ window.offset = out.physical.offset ∧
      CandidateCallBindings.WindowBinding post window.pointer window.id window.offset.toNat 1 ∧
      CurrentCallBoolProtection.WindowReady post window.id window.offset.toNat 1 := by
  obtain ⟨_,_,_,idEq,offsetEq,offsetNat,extra,_,ready,binding,_,_,_,_,mutation⟩ := facts
  let written := (CurrentCallEmptyEntryCompleteRelease.written out.certificate.output (UInt64.ofNat call.returnOffset)).tree
  have allocationEq : out.updated.setExtra written = out.updated := by
    have same : out.updated.extra = written := extra
    rw [←same]
    exact (fun (allocation : Allocation Provenance BorrowTree) => show allocation.setExtra allocation.extra = allocation from by cases allocation; rfl) out.updated
  have initialLive : (machine out count).memory.live.find? (fun row => row.1 == out.physical.id) =
      some (out.physical.id,{out.physical.entry with allocation:=out.updated.setExtra written}) := by
    rw [allocationEq]
    exact CurrentCallEmptyEntryNonzeroHeap.initial_live out count
  have initialBinding : CandidateCallBindings.WindowBinding (machine out count) out.physical.pointer out.physical.id out.physical.offset.toNat 1 := by
    rw [idEq,offsetNat]
    exact binding
  have initialReady : CurrentCallBoolProtection.WindowReady (sourceMachine out) out.physical.id out.physical.offset.toNat 1 := by
    rw [idEq,offsetNat]
    exact ready.bool.transport rfl
  obtain ⟨initial,pointer,id,offset,_,initialBinding,_⟩ := CurrentCallEmptyEntryReturnWindow.of_mutation
    out.physical written written out.updated (by rw [offsetEq]; exact mutation)
    initialLive rfl initialBinding initialReady rfl
  have finish : ∀ window : CurrentCallBoolScalarWrite.Window post place,
      window.pointer = initial.pointer → window.id = initial.id → window.offset = initial.offset →
      CandidateCallBindings.WindowBinding post window.pointer window.id window.offset.toNat 1 →
      ∃ window : CurrentCallBoolScalarWrite.Window post place,
        window.pointer = out.physical.pointer ∧ window.id = out.physical.id ∧ window.offset = out.physical.offset ∧
        CandidateCallBindings.WindowBinding post window.pointer window.id window.offset.toNat 1 ∧
        CurrentCallBoolProtection.WindowReady post window.id window.offset.toNat 1 := by
    intro window pointerNext idNext offsetNext bindingNext
    refine ⟨window,pointerNext.trans pointer,idNext.trans id,offsetNext.trans offset,bindingNext,?_⟩
    rw [idNext,id,offsetNext,offset,idEq,offsetNat]
    exact body.ready.bool
  rcases body.heap with unchanged | changed
  · obtain ⟨window,pointerNext,idNext,offsetNext,_,bindingNext⟩ := CurrentCallRootPhysicalWindow.view initial initialBinding
      body.addresses (congrArg (fun memory => memory.live) unchanged)
    exact finish window pointerNext idNext offsetNext bindingNext
  · obtain ⟨heap⟩ := changed
    let second := S03EmptyNextLenInput.form heap.entry.allocation.extra (held out).global heap.runtime
      tracker.global.nextPointerTag heap.first heap.fresh heap.room
    obtain ⟨window,pointerNext,idNext,offsetNext,bindingNext⟩ := CurrentCallRootPhysicalWindow.tree_update initial initialBinding
      heap.id heap.entry second.after heap.live body.addresses (by rw [heap.memory]; rfl)
    exact finish window pointerNext idNext offsetNext bindingNext

end
end DuplicatePrefix.CurrentCallEmptyEntryNonzeroWindow

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryNonzeroWindow" then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved nonzero window dependency {dependency}"
