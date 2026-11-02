import duplicate_prefix.GeneralBorrowPositiveConcreteWindowAcceptedInitialActivity
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableAcceptedTargetActivity
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowAcceptedCopyStage
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowAcceptedCopyRestore
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowAcceptedExitInput
namespace DuplicatePrefix.GeneralBorrowPositiveConcreteWindowAccepted
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open GeneralBorrowFreshActiveWithin
open ActualReferenceContext GeneralBorrowExposedScopedInactiveWritableAsMutCallReturn GeneralBorrowExposedScopedInactiveWritableAsMutToCopy
variable [area : GeneralBorrowExposedKnownRootState.Scope]
variable {profileMode : ProfileMode}
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- Original physical accepted invocation through both helpers and the actual
copy, with all mixed root-release data formed for the final physical return. -/
theorem prepare (s : GeneralBorrowPositiveConcreteWindowAcceptedCompleteInput.InitialFor profileMode) :
    ∃ (input : GeneralBorrowScopedInactiveWritableRootPhysicalExit.Input) (installed : MachineHooks.State MiriMemoryKind Machine.RootUser),
      input.options=s.options ∧ input.limits=s.limits ∧ input.remaining=s.remaining ∧ input.span=s.span ∧
      Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,
          .Copy (EmptyRootArguments.second s.count)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩=.ok () installed ∧
      SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits installed
        (Storage.withCurrent #[] (GeneralBorrowScopedInactiveWritableRootPhysicalExit.caller input) input.machine) := by
  obtain ⟨p⟩ := GeneralBorrowPositiveConcreteWindowAcceptedCopyStage.forms s
  obtain ⟨output⟩ := GeneralBorrowPositiveConcreteWindowAcceptedCopyStage.run s p
  let source:=GeneralBorrowPositiveConcreteWindowAcceptedCallSource.build s.toAccepted p.updated p.i p.stage p.expression p.call p.origin p.expressionOrigin p.callOrigin
  have trackerEq:=GeneralBorrowPositiveConcreteWindowAcceptedCopyData.tracker_eq p.call p.root p.post p.tracked p.copy
  have treeEq : output.result.extra=GeneralBorrowPositiveConcreteWindowAcceptedCopyRestore.copiedTree p.call := by
    unfold GeneralBorrowPositiveConcreteWindowAcceptedCopyRestore.copiedTree
    rw [output.tree]
    change (((released p.call.toInput).performBorrowAccessRange (.concrete p.call.tracker.global.nextPointerTag)
      (Size.ofBytes p.call.offset) (Size.ofBytes p.call.count) .Read p.copy.tracker.global.protectedTags .VisitChildrenOfAccessed).tree.performBorrowAccessRange
      (.concrete p.call.tracker.global.nextPointerTag) (Size.ofBytes (p.call.offset+p.call.count)) (Size.ofBytes p.call.count) .Write p.copy.tracker.global.protectedTags .VisitChildrenOfAccessed).tree=_
    rw [trackerEq]
  have strong : GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty
      (GeneralBorrowExposedScopedInactiveWritableAccessData.Data (GeneralBorrowPositiveConcreteWindowAcceptedCopyRestore.copiedTree p.call) location
        (GeneralBorrowPositiveConcreteWindowAcceptedCopyRestore.ended p.call).protectedTags
        (GeneralBorrowFreshMetadataChildMutable.index p.call.data.input) p.call.selected p.call.head p.call.tail
        (fun position=>p.call.data.resources.component.support position ∨position=(GeneralBorrowFreshMetadataChildMutable.index p.call.data.input).toNat)))
      p.call.offset (p.call.offset+p.call.len) (GeneralBorrowPositiveConcreteWindowAcceptedCopyRestore.copiedTree p.call).locations := by
    have h:=output.strong
    change GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty
      (GeneralBorrowExposedScopedInactiveWritableAccessData.Data output.result.extra location p.copy.tracker.global.protectedTags
        (GeneralBorrowFreshMetadataChildMutable.index p.call.data.input) p.call.selected p.call.head p.call.tail
        (fun position=>p.call.data.resources.component.support position ∨position=(GeneralBorrowFreshMetadataChildMutable.index p.call.data.input).toNat)))
      p.call.offset (p.call.offset+p.call.len) output.result.extra.locations at h
    rw [treeEq,trackerEq] at h
    exact h
  obtain ⟨_,_,_,fits,tagged,hidden,⟨targetContext⟩,owned⟩ := GeneralBorrowPositiveConcreteWindowAcceptedCopyRestore.restore
    s.toAccepted p.updated p.i p.stage p.expression p.call p.origin p.expressionOrigin p.callOrigin p.context strong
  have capacity : output.result.extra.locations.size.bytes=s.capacity := by
    have same:=congrArg Size.bytes (output.capacity.trans p.capacity)
    calc
      output.result.extra.locations.size.bytes=p.call.entry.allocation.extra.locations.size.bytes:=same
      _ =p.call.entry.allocation.byteSize.bytes:=congrArg Size.bytes p.call.capacity
      _ =s.entry.allocation.byteSize.bytes:=congrArg Size.bytes source.bufferSize
      _ =s.capacity:=by rw [s.bufferSize];rfl
  have initialActivity:=GeneralBorrowPositiveConcreteWindowAcceptedInitialActivity.source s.toAccepted
    p.updated p.i p.stage p.expression p.origin p.expressionOrigin p.firstOffset p.firstLen
  have actualActivity:=GeneralBorrowExposedScopedInactiveWritableAcceptedTargetActivity.after_copy p.expression p.call.toInput
    p.callOrigin initialActivity p.call.count p.call.within
  have activityTree : GeneralBorrowExposedScopedInactiveWritableAcceptedTargetActivity.copiedTree p.call.toInput p.call.count=GeneralBorrowPositiveConcreteWindowAcceptedCopyRestore.copiedTree p.call := rfl
  rw [activityTree] at actualActivity
  have active : ActiveWithin output.result.extra p.expression.data.input.parent .Write s.offset (s.offset+s.len) := by
    rw [treeEq]
    change ActiveWithin (GeneralBorrowPositiveConcreteWindowAcceptedCopyRestore.copiedTree p.call)
      p.expression.data.input.parent .Write s.offset (s.offset+s.len)
    simpa only [p.expressionOrigin.offset,p.expressionOrigin.len,p.origin.offset,p.origin.len] using actualActivity
  have targetHidden : targetContext.anchorNode.isExposed=false := by
    obtain ⟨node,present,_,notExposed⟩:=hidden
    have same:=Option.some.inj (targetContext.anchorPresent.symm.trans present)
    exact same ▸ notExposed
  let resultContext : GeneralBorrowExposedKnownRootRangeData.Context output.result.extra p.expression.data.input.parent p.call.selected p.call.head p.call.tail := {
    anchorNode:=targetContext.anchorNode,selectedNode:=targetContext.selectedNode,
    anchorPresent:=by rw [treeEq];exact targetContext.anchorPresent,
    selectedPresent:=by rw [treeEq];exact targetContext.selectedPresent,
    roots:=by rw [treeEq];exact targetContext.roots,
    depth:=by rw [treeEq];exact targetContext.depth,
    children:=by rw [treeEq];exact targetContext.children,
    tags:=by rw [treeEq];exact targetContext.tags }
  let postcopy : GeneralBorrowPositiveConcreteWindowAcceptedExitInput.PostCopy s.toAccepted := {
    updated:=p.updated,call:=p.call,source:=source,root:=p.root,post:=p.post,shape:=p.shape,memory:=p.memory,tracked:=p.tracked,runtime:=p.runtime,
    copy:=p.copy,data:=GeneralBorrowPositiveConcreteWindowAcceptedCopyStage.data s p,dataId:=source.id,output:=output,
    target:=p.expression.data.input.parent,selected:=p.call.selected,head:=p.call.head,tail:=p.call.tail,
    context:=resultContext,
    support:=(fun position=>p.call.data.resources.component.support position ∨position=(GeneralBorrowFreshMetadataChildMutable.index p.call.data.input).toNat),
    hidden:=targetHidden,
    tagged:=by rw [treeEq];exact tagged,
    owned:=by rw [treeEq,trackerEq];exact owned,
    fits:=by rw [treeEq];exact fits,capacity:=capacity,active:=active }
  obtain ⟨input,options,limits,remaining,span,caller,machine⟩:=GeneralBorrowPositiveConcreteWindowAcceptedExitInput.build s.toAccepted postcopy
  have copyTrace : SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits
      (Storage.withCurrent #[] p.root p.post)
      (Storage.withCurrent #[] (CopyRootOutput.caller p.root p.copy.valid) output.finalMachine) := by
    simpa only [source.options,source.limits,source.remaining,source.span] using output.trace
  have fullTrace:=SuccessfulTrace.append p.trace copyTrace
  refine ⟨input,p.installed,options,limits,remaining,span,p.originalCall,?_⟩
  rw [caller,machine]
  exact fullTrace
end
end DuplicatePrefix.GeneralBorrowPositiveConcreteWindowAccepted
