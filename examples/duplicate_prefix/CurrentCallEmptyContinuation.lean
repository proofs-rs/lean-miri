import duplicate_prefix.CurrentCallEmptyLedgerRelease
import duplicate_prefix.CurrentCallResourceRootFinish
import duplicate_prefix.DuplicatePrefixArgumentCallResult
import duplicate_prefix.CurrentCallEmptyProtocolControl
namespace DuplicatePrefix.CurrentCallEmptyContinuation
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- One actual root-return boundary for every empty-source representation.
The source contributes only its real optional ledger, never byte ownership.
The original destination is a pointer, so a latent initial Bool needs no
fabricated pre-materialization window. All fields describe this SAME machine. -/
structure Core (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (place : MPlaceTy Provenance) (machine : Before) (tracker : MachineHooks.BorrowState)
    (data : Identities) (owner : Nat) (id : AllocId) (offset : Nat)
    (original : PointerInstance) (B : UniformWindow machine tracker data owner id offset 1 .ret)
    (physical : CurrentCallBoolScalarWrite.Window machine place) where
  originalId : original.allocation=id
  binding : CandidateCallBindings.WindowBinding machine physical.pointer physical.id physical.offset.toNat 1
  idEq : physical.id=id
  offsetEq : physical.offset.toNat=offset
  pointerEq : physical.pointer=original.value
  allocationEq : physical.entry.allocation=B.allocation
  parentIssued : SpatialDelegation machine tracker id B.allocation B.precise.completion original.grant
  parentBinding : PointerBinds B.allocation original
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global
  roots : B.allocation.extra.roots.toList.Nodup
  short : B.allocation.extra.nodes.size<65536
  concrete : ∃supplied tag,B.pointer.value.provenance=.concrete supplied tag
  node : TreeNode
  nodeAt : B.allocation.extra.nodes.get B.pointer.grant=some node
  hidden : node.isExposed=false
  active : GeneralBorrowFreshActiveWithin.ActiveWithin B.allocation.extra B.pointer.grant .Write physical.offset (physical.offset+1)
  source : Option (AllocId × BorTag)
  ledger : CurrentCallEmptyLedgerRelease.SourceLedger machine B.allocation.extra source
  borrowFrame : FrameState
  tags : borrowFrame.protectedTags=CurrentCallEmptyLedgerRelease.rows source id node.tag
  edge : B.precise.completion.parents[B.pointer.grant.toNat]?=some (some original.grant)
  model : DuplicatePrefixCallModel.Model options remaining span machine
  tracked : machine.borrowTracker=some tracker
  thread : Miri.Concurrency.ThreadRecord
  activeThread : machine.threads.activeThread?=some thread
  physicalReady : CurrentCallBoolProtection.WindowReady machine physical.id physical.offset.toNat 1


/-- Current resource/metadata transport through a real heap-preserving control
step. This covers every optional source ledger without source-kind cases. -/
theorem Core.view {options remaining span place machine tracker data owner id offset original B physical}
    (core : Core options remaining span place machine tracker data owner id offset original B physical)
    (post : Before) (memory : post.memory=machine.memory) (addresses : post.user.addresses=machine.user.addresses)
    (extras : post.user.payload.payload.user.runtime.extras=machine.user.payload.payload.user.runtime.extras)
    (model : DuplicatePrefixCallModel.Model options remaining span post) (tracked : post.borrowTracker=some tracker)
    (thread : Miri.Concurrency.ThreadRecord) (active : post.threads.activeThread?=some thread) :
    ∃Q : UniformWindow post tracker data owner id offset 1 .ret,∃P : CurrentCallBoolScalarWrite.Window post place,
      ∃next : Core options remaining span place post tracker data owner id offset original Q P,
        next.source=core.source ∧next.borrowFrame=core.borrowFrame ∧next.node=core.node := by
  have present : Present (ActualWorld post) id B.allocation := by unfold Present ActualWorld;rw [memory];exact B.present
  let Q : UniformWindow post tracker data owner id offset 1 .ret:={B with
    present:=present
    issued:=CurrentCallAllocationLicense.spatial B.issued post tracker B.allocation present rfl rfl rfl rfl
      (by intro position root found;exact found) (by intro index node found;exact ⟨node,found,rfl,rfl,rfl,rfl⟩)
      B.precise.completion (by intro first second edge;exact edge)}
  obtain ⟨P,pointerEq,idEq,offsetEq,entryEq,binding⟩:=CurrentCallRootPhysicalWindow.view (final:=post) physical core.binding addresses (congrArg MemoryState.live memory)
  have parent:=CurrentCallAllocationLicense.spatial core.parentIssued post tracker B.allocation present rfl rfl rfl rfl
    (by intro position root found;exact found) (by intro index node found;exact ⟨node,found,rfl,rfl,rfl,rfl⟩)
    B.precise.completion (by intro first second edge;exact edge)
  let next : Core options remaining span place post tracker data owner id offset original Q P:={
    originalId:=core.originalId,binding:=binding,idEq:=idEq.trans core.idEq,offsetEq:=(congrArg UInt64.toNat offsetEq).trans core.offsetEq,
    pointerEq:=pointerEq.trans core.pointerEq,allocationEq:=(congrArg LocalAllocation.allocation entryEq).trans core.allocationEq,
    parentIssued:=parent,parentBinding:=core.parentBinding,runtime:=core.runtime,roots:=core.roots,short:=core.short,concrete:=core.concrete,
    node:=core.node,nodeAt:=core.nodeAt,hidden:=core.hidden,active:=by rw [offsetEq];exact core.active,
    source:=core.source,ledger:=core.ledger.transport memory,borrowFrame:=core.borrowFrame,tags:=core.tags,edge:=core.edge,
    model:=model,tracked:=tracked,thread:=thread,activeThread:=active,physicalReady:=by rw [idEq,offsetEq];exact core.physicalReady.transport extras}
  exact ⟨Q,P,next,rfl,rfl,rfl⟩

structure Ready (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (place : MPlaceTy Provenance) (machine : Before) (tracker : MachineHooks.BorrowState)
    (data : Identities) (owner : Nat) (id : AllocId) (offset : Nat)
    (original : PointerInstance) (B : UniformWindow machine tracker data owner id offset 1 .ret)
    (physical : CurrentCallBoolScalarWrite.Window machine place) (frame : CompilerFrameContext.ActualFrame) extends Core options remaining span place machine tracker data owner id offset original B physical where
  frameTracked : frame.extra.borrowTracker=some borrowFrame
  body : frame.body=RootBody.reflected.body.body
  location : frame.location=.mir ⟨10,0⟩
  size : frame.locals.size=25
  noClocks : frame.extra.dataRace=none
  stop : frame.returnContinuation=.stop true
  varargs : frame.vaList=#[]
  immediate : CopyHelperCleanup.AllImmediate frame
  value : Bool
  slot0 : frame.locals[0]?=some ⟨.live (.immediate (.scalar (.fromBool value))),some RootCompilerFacts.boolLayout⟩
  destination : frame.returnPlace.toRuntimePlace=⟨.memory place.mplace,place.layout⟩

/-- Release classification is internal. This executes the actual whole-frame
endCall, original Bool store and terminal pop with one common return rule. -/
theorem finish {options remaining span place machine tracker data owner id offset original B physical frame}
    (ready : Ready options remaining span place machine tracker data owner id offset original B physical frame)
    (limits : ExecutionMachine.Limits) (fuel : Nat) (fuelEq : options.limits.validation=fuel+1) :
    ∃final,SuccessfulTrace.Trace (config options (remaining+1) span) limits (Storage.withCurrent #[] frame machine) final ∧
      ExecutionMachine.step (config options (remaining+1) span) limits () final=(final,.ok false) ∧final.stack.frames=#[] := by
  have live : machine.memory.live.find? (fun row=>row.1==id)=some (id,physical.entry) := by rw [←ready.idEq];exact physical.live
  obtain ⟨released⟩:=CurrentCallEmptyLedgerRelease.release B ready.runtime ready.roots ready.short ready.concrete ready.node ready.nodeAt ready.hidden
    ready.ledger ready.borrowFrame ready.tags original.grant ready.edge physical.offset ready.offsetEq ready.active physical.entry live ready.allocationEq
  exact CurrentCallResourceRootFinish.finish_pointer options limits remaining span place original ready.originalId B physical ready.binding ready.idEq ready.offsetEq
    ready.pointerEq ready.parentIssued ready.parentBinding frame ready.borrowFrame released ready.model ready.tracked ready.frameTracked ready.thread ready.activeThread
    ready.body ready.location ready.size ready.noClocks ready.stop ready.varargs ready.immediate ready.value ready.slot0 ready.destination ready.physicalReady fuel fuelEq

/-- The derived entry equation and derived body prefix feed the same common
continuation. This assembles the original call Result, including every
reachable prefix; no source representation is chosen by this consumer. -/
theorem result {options remaining span place machine tracker data owner id offset original B physical frame}
    (ready : Ready options remaining span place machine tracker data owner id offset original B physical frame)
    (limits : ExecutionMachine.Limits) (fuel : Nat) (fuelEq : options.limits.validation=fuel+1)
    (before : Before) (argument : DuplicatePrefixSliceArgument.Argument) (count : UInt64)
    (entryFrame : CompilerFrameContext.ActualFrame) (entryMachine : Before)
    (entered : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base argument 0),.Copy (EmptyRootArguments.second count)]
      false (.memory place) (.stop true) (⟨⟨#[]⟩,before⟩ : RootState)=.ok () (Storage.withCurrent #[] entryFrame entryMachine))
    (bodyTrace : SuccessfulTrace.Trace (config options (remaining+1) span) limits (Storage.withCurrent #[] entryFrame entryMachine)
      (Storage.withCurrent #[] frame machine)) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument 0 count place := by
  obtain ⟨final,returned,terminal,emptyStack⟩:=finish ready limits fuel fuelEq
  let start:=Storage.withCurrent #[] entryFrame entryMachine
  have trace : SuccessfulTrace.Trace (config options (remaining+1) span) limits start final:=SuccessfulTrace.append bodyTrace returned
  let context : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit:=⟨config options (remaining+1) span,limits,fun _ _=>True⟩
  have callEntry : CallSafety.IsCallEntry 1 start:=⟨by decide,rfl⟩
  have past : CallSafety.pastCallBoundary 1 final:=by change final.stack.frames.size<1;rw [emptyStack];decide
  exact ⟨start,final,entered,trace,terminal,emptyStack,
    SuccessfulTrace.no_errors context 1 start final callEntry trace past,
    SuccessfulTrace.no_ub context 1 start final callEntry trace past,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

private theorem tick_model (options remaining span machine)
    (model : DuplicatePrefixCallModel.Model options remaining span machine) :
    DuplicatePrefixCallModel.Model options remaining span (RootZeroCompleteState.tick options remaining span machine) := by
  have flags:=RootZeroCompleteState.tick_flags options remaining span machine
  have unchecked:=model.unchecked
  have noGc:=model.noGc
  rw [(actual_fields options () (remaining+1) span).terminators] at unchecked noGc
  unfold RootZeroCompleteState.tick SourceControl.accounted at flags ⊢
  rw [(actual_fields options () (remaining+1) span).terminators] at flags ⊢
  exact {model with
    unchecked:=by rw [(actual_fields options () (remaining+1) span).terminators];exact flags.1.trans unchecked
    noGc:=by rw [(actual_fields options () (remaining+1) span).terminators];exact flags.2.trans noGc}

/-- One count-zero continuation for ALL actual source representations and
optional source ledgers. It internally constructs the real prefix and release. -/
theorem zero {options remaining span place machine tracker data owner id offset original B physical}
    (core : Core options remaining span place machine tracker data owner id offset original B physical)
    (limits : ExecutionMachine.Limits) (root : RootFrameData.RootFrame) (updated : Immediate Provenance) (sourceFrame : FrameState)
    (raw : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (borrow : core.borrowFrame=sourceFrame.addProtector id core.node.tag)
    (stop : root.frame.returnContinuation=.stop true)
    (destination : root.frame.returnPlace.toRuntimePlace=⟨.memory place.mplace,place.layout⟩) (varargs : root.frame.vaList=#[])
    (fuel : Nat) (fuelEq : options.limits.validation=fuel+1) :
    ∃final,SuccessfulTrace.Trace (config options (remaining+1) span) limits
      (Storage.withCurrent #[] (CurrentCallEmptyProtocolControl.frame root updated sourceFrame 0 id core.node.tag) machine) final ∧
      ExecutionMachine.step (config options (remaining+1) span) limits () final=(final,.ok false) ∧final.stack.frames=#[] := by
  let entry:=CurrentCallEmptyProtocolControl.frame root updated sourceFrame 0 id core.node.tag
  obtain ⟨frame,bodyTrace,body,identity,callee,size,located,slot0,returnPlace,extra,continuation,va,immediate⟩:=
    CurrentCallEmptyProtocolControl.zero_prefix options limits remaining span root updated sourceFrame id core.node.tag raw machine core.model fuel fuelEq
  let post:=RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span machine)
  have memory : post.memory=machine.memory := by unfold post RootZeroCompleteState.tick SourceControl.accounted;rw [(actual_fields options () (remaining+1) span).terminators] <;>rfl
  have addresses : post.user.addresses=machine.user.addresses := by unfold post RootZeroCompleteState.tick SourceControl.accounted;rw [(actual_fields options () (remaining+1) span).terminators] <;>rfl
  have extras : post.user.payload.payload.user.runtime.extras=machine.user.payload.payload.user.runtime.extras := by unfold post RootZeroCompleteState.tick SourceControl.accounted;rw [(actual_fields options () (remaining+1) span).terminators] <;>rfl
  have tracked : post.borrowTracker=some tracker := by unfold post RootZeroCompleteState.tick SourceControl.accounted;rw [(actual_fields options () (remaining+1) span).terminators];exact core.tracked
  have active : post.threads.activeThread?=some core.thread := by unfold post RootZeroCompleteState.tick SourceControl.accounted;rw [(actual_fields options () (remaining+1) span).terminators];exact core.activeThread
  obtain ⟨Q,P,next,sourceEq,borrowEq,nodeEq⟩:=core.view post memory addresses extras
    (tick_model options remaining span _ (tick_model options remaining span _ core.model)) tracked core.thread active
  have metadata:=CurrentCallEmptyProtocolControl.metadata root updated sourceFrame 0 id core.node.tag
  have ready : Ready options remaining span place post tracker data owner id offset original Q P frame:={
    toCore:=next,
    frameTracked:=by rw [borrowEq,borrow,extra];exact metadata.2.2.2.2.2.2.2.1,
    body:=body,location:=located,size:=size,noClocks:=by rw [extra];exact metadata.2.2.2.2.2.2.1.trans root.noClocks,
    stop:=continuation.trans (metadata.2.2.2.1.trans stop),varargs:=va.trans (metadata.2.2.2.2.2.1.trans varargs),immediate:=immediate,
    value:=true,slot0:=slot0,destination:=by rw [returnPlace,metadata.2.2.2.2.1];exact destination}
  obtain ⟨final,returned,terminal,emptyStack⟩:=finish ready limits fuel fuelEq
  exact ⟨final,SuccessfulTrace.append bodyTrace returned,terminal,emptyStack⟩
end
end DuplicatePrefix.CurrentCallEmptyContinuation
