import duplicate_prefix.CurrentCallEmptyEntryNonzeroReturn
import duplicate_prefix.CurrentCallEmptyEntryNonzeroPlan
import duplicate_prefix.CurrentCallEmptyEntryNonzeroHeap
import duplicate_prefix.CurrentCallEmptyEntryReturnWindow
import duplicate_prefix.CurrentCallEmptyEntryNonzeroSourceRelease
import duplicate_prefix.CurrentCallEmptyEntryNonzeroWindow
import duplicate_prefix.CurrentCallEmptyEntryNonzeroCurrentHoldings
import duplicate_prefix.CurrentCallEmptyEntryNonzeroBorrowRelease

namespace DuplicatePrefix.CurrentCallEmptyNonzeroSafety
open Miri Miri.ABI Miri.Memory Miri.Input Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CanonicalConfigFacts
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency true
set_option backward.dsimp.instances false
noncomputable section

variable {options limits remaining span before tracker argument place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data}

private theorem finish (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64)
    (facts : CurrentCallEmptyEntryRoot.Facts out count)
    (result : CompilerFrameContext.ActualFrame) (post : Before)
    (body : CurrentCallEmptyEntryNonzeroDispatch.BodyResult out count result post)
    (current : MachineHooks.BorrowState) (tracked : post.borrowTracker=some current)
    (window : CurrentCallBoolScalarWrite.Window post place)
    (windowId : window.id=out.physical.id)
    (binding : CandidateCallBindings.WindowBinding post window.pointer window.id window.offset.toNat 1)
    (ready : CurrentCallBoolProtection.WindowReady post window.id window.offset.toNat 1)
    (released : BorrowTree)
    (boolRelease : window.entry.allocation.extra.releaseProtector out.certificate.output.tag current.global.protectedTags=⟨released,.Released⟩)
    (originalWrite : (released.performBorrowAccessRange (S04ReturnBorrowBridge.extra window.pointer.provenance)
      (Size.ofBytes window.offset) (Size.ofBytes 1) .Write
      (current.global.endCall out.certificate.output.frame).protectedTags .VisitChildrenOfAccessed).status=.Completed) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument 0 count place := by
  have sourceRelease := CurrentCallEmptyEntryNonzeroSourceRelease.source_release out count facts result post body
  have sameRelease : out.effect.allocation=some window.id →
      window.entry.allocation.extra.releaseProtector tracker.global.nextPointerTag current.global.protectedTags=⟨window.entry.allocation.extra,.Released⟩ := by
    intro allocated
    rcases sourceRelease window.id allocated current.global.protectedTags with ⟨info,lookup,notLive⟩ | ⟨source,found,quiet⟩
    · rw [MemoryState.getAllocInfo,window.live] at lookup
      cases lookup
      exact False.elim (notLive rfl)
    · have same : source=window.entry := (Prod.mk.inj (Option.some.inj (found.symm.trans window.live))).2
      subst source
      exact quiet
  obtain ⟨releasedMemory,plan,lastBool⟩ := CurrentCallEmptyEntryNonzeroPlan.construct post.memory out.effect.allocation
    tracker.global.nextPointerTag current.global.protectedTags window.id out.certificate.output.tag window.entry released window.live boolRelease
    sameRelease (by intro q allocated _;exact sourceRelease q allocated current.global.protectedTags)
  have rows : out.certificate.output.frame.protectedTags.toList=
      (out.effect.allocation.toList.map fun q=>(q,tracker.global.nextPointerTag))++[(window.id,out.certificate.output.tag)] := by
    rw [out.certificate.frameEq]
    simp only [FrameState.addProtector,Array.toList_push]
    rw [out.certificate.tag,windowId]
    cases allocation : out.effect.allocation <;> simp [CurrentCallEmptyEntryBool.rootSource,allocation] <;> rfl
  rw [←rows] at plan
  obtain ⟨thread,active⟩ := body.active
  let accounted := S04FinalReturnRuleAccounting.machine options remaining span result post
  let state : RootState := ⟨⟨#[]⟩,GenericPopFrame.afterRelevanceAt #[] result
    (ActualPopPlan.released accounted releasedMemory current out.certificate.output.frame) (thread.topUserRelevantFrame.getD 0)⟩
  have stateUser : state.machine.user=accounted.user := by
    unfold state GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have stateMemory : state.machine.memory=releasedMemory := by
    unfold state GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have metadata := S04FinalReturnRuleAccounting.metadata options remaining span result post
  obtain ⟨finalWindow,pointerEq,idEq,offsetEq,finalBinding⟩ := CurrentCallRootPhysicalWindow.plan current.global.protectedTags
    out.certificate.output.frame.protectedTags.toList post.memory releasedMemory plan post state.machine rfl stateMemory
    (by rw [stateUser];exact metadata.1) place window binding
  have finalReady : CurrentCallBoolProtection.WindowReady state.machine finalWindow.id finalWindow.offset.toNat 1 := by
    rw [idEq,offsetEq]
    apply ready.transport
    rw [stateUser]
    exact metadata.2.2.2.2
  have finalLive := finalWindow.live
  rw [stateMemory,idEq,lastBool] at finalLive
  have entryEq : finalWindow.entry={window.entry with allocation:=window.entry.allocation.setExtra released} :=
    (Prod.mk.inj (Option.some.inj finalLive)).2.symm
  have completed : (finalWindow.entry.allocation.extra.performBorrowAccessRange (S04ReturnBorrowBridge.extra finalWindow.pointer.provenance)
      (Size.ofBytes finalWindow.offset) (Size.ofBytes 1) .Write
      (current.global.endCall out.certificate.output.frame).protectedTags .VisitChildrenOfAccessed).status=.Completed := by
    simpa only [entryEq,pointerEq,offsetEq,Allocation.setExtra,Allocation.mapExtra] using originalWrite
  exact CurrentCallEmptyEntryNonzeroReturn.of_plan input out count facts result post body current tracked releasedMemory plan
    thread active state rfl finalWindow finalBinding finalReady completed

private theorem from_body (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64)
    (facts : CurrentCallEmptyEntryRoot.Facts out count)
    (result : CompilerFrameContext.ActualFrame) (post : Before)
    (body : CurrentCallEmptyEntryNonzeroDispatch.BodyResult out count result post) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument 0 count place := by
  obtain ⟨window,pointerEq,windowId,windowOffset,binding,ready⟩ := CurrentCallEmptyEntryNonzeroWindow.of_body out count facts result post body
  obtain ⟨current,tracked,_,globalEq,flags,_⟩ := body.tracked
  have flagsEq : current.global.protectedTags=out.certificate.output.global.protectedTags := flags
  have finalProtected : (current.global.endCall out.certificate.output.frame).protectedTags=
      (out.certificate.output.global.endCall out.certificate.output.frame).protectedTags := by
    rw [globalEq]
    rfl
  have offsetEq : out.physical.offset=UInt64.ofNat call.returnOffset := facts.2.2.2.2.1
  have extra : out.updated.extra=(CurrentCallEmptyEntryCompleteRelease.written out.certificate.output (UInt64.ofNat call.returnOffset)).tree := facts.2.2.2.2.2.2.1
  rcases CurrentCallEmptyEntryNonzeroHeap.bool_live out count result post body with unchanged | changed
  · have found := window.live
    rw [windowId,unchanged] at found
    have entryEq : window.entry={out.physical.entry with allocation:=out.updated} := (Prod.mk.inj (Option.some.inj found)).2.symm
    let released := (CurrentCallEmptyEntryCompleteRelease.released out.certificate.output (UInt64.ofNat call.returnOffset)).tree
    have boolRelease : window.entry.allocation.extra.releaseProtector out.certificate.output.tag current.global.protectedTags=⟨released,.Released⟩ := by
      rw [entryEq,flagsEq]
      change out.updated.extra.releaseProtector out.certificate.output.tag out.certificate.output.global.protectedTags=_
      rw [extra]
      change (CurrentCallEmptyEntryCompleteRelease.released out.certificate.output (UInt64.ofNat call.returnOffset))=⟨released,.Released⟩
      rw [←out.certificate.releaseCompleted]
    have originalWrite : (released.performBorrowAccessRange (S04ReturnBorrowBridge.extra window.pointer.provenance)
        (Size.ofBytes window.offset) (Size.ofBytes 1) .Write
        (current.global.endCall out.certificate.output.frame).protectedTags .VisitChildrenOfAccessed).status=.Completed := by
      rw [pointerEq,windowOffset,offsetEq,finalProtected]
      exact out.certificate.originalWrite
    exact finish out count facts result post body current tracked window windowId binding ready released boolRelease originalWrite
  · obtain ⟨heap,sameId,entryEq,last⟩ := changed
    obtain ⟨next,trackedNext,⟨h⟩,runtime,order,bounds,short⟩ :=
      CurrentCallEmptyEntryNonzeroCurrentHoldings.same_allocation out count facts result post body heap sameId
    have nextEq : next=current := Option.some.inj (trackedNext.symm.trans tracked)
    subst next
    let after := CurrentCallEmptyEntryNonzeroCurrentHoldings.after heap
    have found := window.live
    rw [windowId,last] at found
    have windowEntry : window.entry={out.physical.entry with allocation:=out.updated.setExtra after} :=
      (Prod.mk.inj (Option.some.inj found)).2.symm
    have windowTree : window.entry.allocation.extra=after := by rw [windowEntry];rfl
    have hiddenInitial : S04ReturnReleaseParent.HiddenFrame heap.entry.allocation.extra out.certificate.output.frame := by
      rw [entryEq]
      change S04ReturnReleaseParent.HiddenFrame out.updated.extra out.certificate.output.frame
      rw [extra]
      exact out.certificate.hidden
    have hidden : S04ReturnReleaseParent.HiddenFrame after out.certificate.output.frame :=
      S03EmptyPositiveTreeFacts.hidden_frame heap.runtime tracker.global.nextPointerTag heap.first heap.fresh heap.room
        out.certificate.output.frame hiddenInitial
    have member : (out.physical.id,out.certificate.output.tag)∈out.certificate.output.frame.protectedTags.toList := by
      rw [out.certificate.frameEq,out.certificate.tag]
      change (out.physical.id,_)∈((CurrentCallEmptyEntryBool.rootSource out.effect).protectedTags.push (out.physical.id,_)).toList
      rw [Array.toList_push]
      exact List.mem_append.mpr (.inr (by simp))
    have rule := CurrentCallEmptyEntryNonzeroBorrowRelease.release after current.global out.certificate.output.frame out.physical.id
      out.certificate.output.tag tracker.global.nextPointerTag out.physical.pointer.provenance (UInt64.ofNat call.returnOffset)
      h runtime order bounds short member hidden
    let released := (after.releaseProtector out.certificate.output.tag current.global.protectedTags).tree
    have boolRelease : window.entry.allocation.extra.releaseProtector out.certificate.output.tag current.global.protectedTags=⟨released,.Released⟩ := by
      rw [windowTree]
      rw [←rule.completed]
    have originalWrite : (released.performBorrowAccessRange (S04ReturnBorrowBridge.extra window.pointer.provenance)
        (Size.ofBytes window.offset) (Size.ofBytes 1) .Write
        (current.global.endCall out.certificate.output.frame).protectedTags .VisitChildrenOfAccessed).status=.Completed := by
      rw [pointerEq,windowOffset,offsetEq]
      exact rule.originalWrite
    exact finish out count facts result post body current tracked window windowId binding ready released boolRelease originalWrite

/-- Actual original empty-source call for every nonzero UInt64 count. The
entry, both helper calls, root release, pop and original Bool store share one trace. -/
theorem invoke
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data)
    (stackReady : CurrentCallPush.StackReadiness before #[])
    (memoryReady : CurrentCallBoolProtection.ProfileMemoryReadiness before call)
    (count : UInt64) (nonzero : count≠0) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument 0 count place := by
  obtain ⟨out,facts⟩ := CurrentCallEmptyEntryRoot.complete input #[] stackReady memoryReady count
  obtain ⟨result,post,body⟩ := CurrentCallEmptyEntryNonzeroDispatch.from_entry out count facts stackReady nonzero
  exact from_body out count facts result post body

end
end DuplicatePrefix.CurrentCallEmptyNonzeroSafety

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyNonzeroSafety" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved original empty nonzero safety dependency {dependency}"
