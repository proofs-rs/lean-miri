import duplicate_prefix.CurrentCallEmptyContinuation
namespace DuplicatePrefix.CurrentCallEmptyPointerReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
/-- Common actual root Return after either empty-source body branch. The
zero source may have descendants; current quiescence suffices to release it.
No source byte authority or family is introduced. -/
theorem finish {boolId boolOffset machine tracker data owner}
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (place : MPlaceTy Provenance)
    (original : PointerInstance) (originalId : original.allocation=boolId)
    (B : UniformWindow machine tracker data owner boolId boolOffset 1 .ret)
    (physical : CurrentCallBoolScalarWrite.Window machine place)
    (binding : CandidateCallBindings.WindowBinding machine physical.pointer physical.id physical.offset.toNat 1)
    (sameId : physical.id=boolId) (sameOffset : physical.offset.toNat=boolOffset)
    (samePointer : physical.pointer=original.value) (sameAllocation : physical.entry.allocation=B.allocation)
    (parentIssued : SpatialDelegation machine tracker boolId B.allocation B.precise.completion original.grant)
    (parentBinding : PointerBinds B.allocation original)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (distinct : B.allocation.extra.roots.toList.Nodup) (short : B.allocation.extra.nodes.size<65536)
    (concrete : ∃ supplied tag,B.pointer.value.provenance=.concrete supplied tag)
    (node : TreeNode) (nodeAt : B.allocation.extra.nodes.get B.pointer.grant=some node) (hidden : node.isExposed=false)
    (activeB : GeneralBorrowFreshActiveWithin.ActiveWithin B.allocation.extra B.pointer.grant .Write physical.offset (physical.offset+1))
    (sourceId : AllocId) (sourceTag : BorTag) (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (sourceLive : machine.memory.live.find? (fun row=>row.1==sourceId)=some (sourceId,sourceEntry))
    (sourceIndex : UniIndex) (sourceNode : TreeNode)
    (sourceTagged : sourceEntry.allocation.extra.indexOfTag sourceTag=some sourceIndex)
    (sourcePresent : sourceEntry.allocation.extra.nodeAt sourceIndex=some sourceNode)
    (sourceHidden : sourceNode.isExposed=false)
    (sourceQuiet : S04ReturnReleaseInactive.Quiescent sourceEntry.allocation.extra sourceIndex)
    (sourceHiddenOnBool : ∀index current,B.allocation.extra.nodes.get index=some current→current.tag=sourceTag→current.isExposed=false)
    (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState)
    (tags : borrowFrame.protectedTags=#[(sourceId,sourceTag),(boolId,node.tag)])
    (frameTracked : frame.extra.borrowTracker=some borrowFrame)
    (body : frame.body=RootBody.reflected.body.body) (location : frame.location=.mir ⟨10,0⟩)
    (size : frame.locals.size=25) (noClocks : frame.extra.dataRace=none)
    (stop : frame.returnContinuation=.stop true) (varargs : frame.vaList=#[])
    (immediate : CopyHelperCleanup.AllImmediate frame) (value : Bool)
    (slot0 : frame.locals[0]?=some ⟨.live (.immediate (.scalar (.fromBool value))),some RootCompilerFacts.boolLayout⟩)
    (destination : frame.returnPlace.toRuntimePlace=⟨.memory place.mplace,place.layout⟩)
    (model : DuplicatePrefixCallModel.Model options remaining span machine) (enabled : machine.borrowTracker=some tracker)
    (thread : Miri.Concurrency.ThreadRecord) (threadAt : machine.threads.activeThread?=some thread)
    (edge : B.precise.completion.parents[B.pointer.grant.toNat]?=some (some original.grant))
    (ready : CurrentCallBoolProtection.WindowReady machine physical.id physical.offset.toNat 1)
    (fuel : Nat) (fuelEq : options.limits.validation=fuel+1) :
    ∃final,SuccessfulTrace.Trace (config options (remaining+1) span) limits (Storage.withCurrent #[] frame machine) final ∧
      ExecutionMachine.step (config options (remaining+1) span) limits () final=(final,.ok false) ∧final.stack.frames=#[] := by
  let after : CurrentCallEmptyContinuation.Ready options remaining span place machine tracker data owner boolId boolOffset original B physical frame:={
    toCore:={
      originalId:=originalId,binding:=binding,idEq:=sameId,offsetEq:=sameOffset,pointerEq:=samePointer,allocationEq:=sameAllocation,
      parentIssued:=parentIssued,parentBinding:=parentBinding,runtime:=runtime,roots:=distinct,short:=short,concrete:=concrete,
      node:=node,nodeAt:=nodeAt,hidden:=hidden,active:=activeB,source:=some (sourceId,sourceTag),
      ledger:=.live sourceId sourceTag sourceEntry sourceLive sourceIndex sourceNode sourceTagged sourcePresent sourceHidden sourceQuiet sourceHiddenOnBool,
      borrowFrame:=borrowFrame,tags:=tags,edge:=edge,model:=model,tracked:=enabled,thread:=thread,activeThread:=threadAt,physicalReady:=ready}
    frameTracked:=frameTracked,body:=body,location:=location,size:=size,noClocks:=noClocks,stop:=stop,varargs:=varargs,
    immediate:=immediate,value:=value,slot0:=slot0,destination:=destination}
  exact CurrentCallEmptyContinuation.finish after limits fuel fuelEq

end
end DuplicatePrefix.CurrentCallEmptyPointerReturn
