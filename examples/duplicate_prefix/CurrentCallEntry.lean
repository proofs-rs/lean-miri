import duplicate_prefix.CurrentCallBoolProtection
import duplicate_prefix.RootEntryTail
import duplicate_prefix.PositiveRootInstalledFrame
import duplicate_prefix.GenericFunctionEntryPrefix

/-! Positive full source Call.initStackFrame. The source argument and Bool
operations retain their actual installed state; entry representation readiness
remains separate from the unadopted current-call resource proposal. -/
namespace DuplicatePrefix.CurrentCallEntry
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall
open CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def root (before : Before) (frames : Array CompilerFrameContext.ActualFrame)
    (place : MPlaceTy Provenance) (race : before.dataRace = none) : RootFrame :=
  RootFrameData.raw (CurrentCallPush.preparedMachine before frames) (CurrentCallArguments.destination place)
    (CallEntryFacts.freshRoot before).2 race

private theorem return_abi (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (state : RootState) :
    (ExecutionMachine.callHooks (config options remaining span) limits).checkArgumentCompat ()
      RootCompilerFacts.rootAbi.ret RootCompilerFacts.rootAbi.ret state = .ok true state := by
  change (config options remaining span).calls.compiler.checkArgumentCompat () _ _ _ = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).callCompiler]
  exact CallEntryFacts.root_return_argument_compat _ options.compatibilityBudget _

/-- The suffix has the exact local-zero span and return ABI query before
protection, then the source preamble/count/afterFrameInit/pushDone sequence. -/
private theorem tail_of_steps (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (root : RootFrame) (machine : Before)
    (place : MPlaceTy Provenance) (after protectedState : RootState)
    (protect : (ExecutionMachine.callHooks (config options remaining span) limits).protectArgument () place
      (Storage.withCurrent frames (atSpan root ⟨601⟩).frame machine) = .ok () protectedState)
    (finish : RootEntryFinish.finish (ExecutionMachine.callHooks (config options remaining span) limits)
      protectedState = .ok () after) :
    RootEntryTail.tail (ExecutionMachine.callHooks (config options remaining span) limits) place
      (Storage.withCurrent frames root.frame machine) = .ok () after := by
  have localSpan := CallEntryLocals.root_span0 options limits remaining span frames root.frame machine root.body root.identity root.callee
  have getFrame := CallEntryLocals.get_frame options limits remaining span frames root.frame machine
  have setFrame := CallEntryLocals.set_frame options limits remaining span frames root.frame (atSpan root ⟨601⟩).frame machine
  have compat := return_abi options limits remaining span (Storage.withCurrent frames (atSpan root ⟨601⟩).frame machine)
  unfold RootEntryTail.tail RootCallCore.spanAt
  simp only [bind,EStateM.bind]
  rw [localSpan]
  dsimp only
  rw [getFrame]
  dsimp only
  dsimp only [atSpan] at setFrame
  rw [setFrame]
  dsimp only
  dsimp only [atSpan] at compat
  rw [compat]
  simp only [EStateM.bind,ite_true]
  dsimp only [atSpan] at protect
  rw [protect]
  exact finish

private theorem argument_slot {options remaining span ctx before tracker frames frame borrowFrame argument len place call data}
    (source : CurrentCallReferenceEntry.ViewedOutcome options remaining span ctx before tracker frames frame borrowFrame
      argument len place call data .FnEntry true)
    (valid : 1 < frame.locals.size) (firstDone : RootFrame)
    (frameEq : firstDone.frame = CurrentCallReferenceEntry.writtenFrame source 1 valid)
    (count : UInt64) (id : Nat) (value : LocalState Provenance LocalLayout)
    (ne1 : id ≠ 1) (ne2 : id ≠ 2) (initial : frame.locals[id]? = some value) :
    (RootArgumentsTwo.result firstDone count).frame.locals[id]? = some value := by
  simpa only [RootArgumentsTwo.result,RootFrameData.write,RootFrameData.live,RootFrameData.cache,RootFrameData.atSpan,
    LocalOperands.cachedLayoutFrame,frameEq,CurrentCallReferenceEntry.writtenFrame,TypedBorrowSteps.registeredFrame,
    TypedRetagEntry.frameWithBorrow,Array.getElem?_set,ne1,ne2,Ne.symm ne1,Ne.symm ne2,ite_false,i2] using initial


/-- One positive actual full initStackFrame, for every UInt64 count. Contexts,
identity allocation, frame/storage facts and both protection operations are
constructed internally. The two execution-readiness predicates remain explicit. -/
theorem invoke (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState) (argument : DuplicatePrefixSliceArgument.Argument)
    (len : UInt64) (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frames : Array CompilerFrameContext.ActualFrame) (stackReady : CurrentCallPush.StackReadiness before frames)
    (memoryReady : CurrentCallBoolProtection.ProfileMemoryReadiness before call)
    (positive : 0 < len.toNat) (count : UInt64) :
    ∃ ctx : ActualReferenceContext.Context options remaining span,
    let machine := CurrentCallPush.preparedMachine before frames
    let initialRoot := root before frames place input.machine.settings.noDataRace
    let prepared := firstLive initialRoot
    ∃ source : CurrentCallReferenceEntry.ViewedOutcome options remaining span ctx machine tracker frames
        (CurrentCallReferenceEntry.copiedFrame options remaining span prepared.frame 1 (prepared.valid i1) argument len)
        {} argument len place call data .FnEntry true,
      ∃ validCopied : 1 < (CurrentCallReferenceEntry.copiedFrame options remaining span prepared.frame 1 (prepared.valid i1) argument len).locals.size,
      ∃ firstDone : RootFrame, ∃ borrowed : CurrentCallBoolProtection.Borrowed source.base.raw,
      ∃ physical : CandidateCurrentBoolUninitWrite.PhysicalWindow (CurrentCallBoolWindow.after source) place,
      ∃ room : source.base.raw.output.global.nextPointerTag.value < 18446744073709551615,
      ∃ updated : Allocation Provenance BorrowTree,
      let changed := atSpan (RootArgumentsTwo.result firstDone count) ⟨601⟩
      let protectedFrame := TypedBorrowSteps.registeredFrame changed.frame source.base.raw.output.frame physical.id source.base.raw.output.global.nextPointerTag
      let retagged := ReturnProtection.borrowedState frames changed.frame source.base.raw.output.frame (CurrentCallBoolWindow.after source)
        ⟨source.base.raw.output.global,tracker.retagMode⟩ room physical.id physical.entry borrowed.output.child.tree
      let finalMachine := {retagged.machine with memory := {retagged.machine.memory with live :=
        ((retagged.machine.memory.live.filter fun row => row.1 != physical.id).push (physical.id,{physical.entry with allocation := updated}))}}
      let finalFrame := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
      firstDone.frame = CurrentCallReferenceEntry.writtenFrame source 1 validCopied ∧
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base argument len), .Copy (second count)]
        false (CurrentCallArguments.destination place) (.stop true) (⟨⟨frames⟩,before⟩ : RootState) =
        .ok () (Storage.withCurrent frames finalFrame finalMachine) ∧
      finalFrame.returnPlace = CurrentCallArguments.destination place ∧
      CurrentCallBoolProtection.Written borrowed ∧
      updated.extra = (CurrentCallBoolProtection.writeResult borrowed).tree ∧
      CandidateCallBindings.WindowBinding finalMachine
        (CurrentCallTypedFnEntry.changedPointer source.base.raw.sourcePointer.value call.sourceId tracker.global.nextPointerTag)
        call.sourceId call.sourceOffset len.toNat ∧
      CurrentCallBoolProtection.ProfileMemoryReadiness finalMachine call ∧
      (call.sourceId = call.returnId → InitMaskCopy.InitializedOn updated.initializationMask
        (Size.ofBytes (UInt64.ofNat call.sourceOffset)) (Size.ofBytes (UInt64.ofNat call.sourceOffset+len))) ∧
      AllocationCopy.snapshot updated = AllocationCopy.snapshot physical.entry.allocation ∧
      physical.id = call.returnId ∧
      physical.pointer = source.base.raw.returnPointer.value ∧
      physical.offset = UInt64.ofNat call.returnOffset ∧
      Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
        ((physical.entry.allocation.setExtra borrowed.output.child.tree).setExtra
          (CurrentCallBoolProtection.writeResult borrowed).tree) = .ok () updated := by
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span input.machine.settings.preciseOff input.machine.settings.implicitOff
  obtain ⟨retagCtx⟩ := ActualRetagContext.exists_context options (remaining+1) span input.machine.settings.preciseOff input.machine.settings.implicitOff
  let machine := CurrentCallPush.preparedMachine before frames
  let transported := CurrentCallPush.prepared_input input frames
  let initialRoot := root before frames place input.machine.settings.noDataRace
  let prepared := firstLive initialRoot
  obtain ⟨source,validCopied,firstDone,frameEq,returnEq,arguments⟩ := CurrentCallArguments.arguments options limits remaining span ctx
    machine tracker argument len place call data transported frames (CallEntryFacts.freshRoot before).2 positive count
  let argsRoot := RootArgumentsTwo.result firstDone count
  let changed := atSpan argsRoot ⟨601⟩
  have frameBorrow : changed.frame.extra.borrowTracker = some source.base.raw.output.frame :=
    CurrentCallBoolProtection.argument_frame source validCopied firstDone frameEq count
  obtain ⟨borrowed,written,physical,room,updated,idEq,pointerEq,offsetEq,protect,extra,mutation,snapshot,readyAfter,sourceBinding,initialized,returnPlace⟩ :=
    CurrentCallBoolProtection.protect_after_source options limits remaining span ctx retagCtx machine tracker argument len place call data
      transported (memoryReady.prepared frames) frames _ {} source changed.frame frameBorrow positive
  let protectedFrame := TypedBorrowSteps.registeredFrame changed.frame source.base.raw.output.frame physical.id source.base.raw.output.global.nextPointerTag
  let retagged := ReturnProtection.borrowedState frames changed.frame source.base.raw.output.frame (CurrentCallBoolWindow.after source)
    ⟨source.base.raw.output.global,tracker.retagMode⟩ room physical.id physical.entry borrowed.output.child.tree
  let finalMachine : Before := {retagged.machine with memory := {retagged.machine.memory with live :=
    ((retagged.machine.memory.live.filter fun row => row.1 != physical.id).push (physical.id,{physical.entry with allocation := updated}))}}
  have dead : ∀ id : Fin 25, id.val ≠ 1 → id.val ≠ 2 →
      (protectedFrame.locals[id.val]'(by simpa only [protectedFrame,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,changed,atSpan] using argsRoot.valid id)).value = .dead := by
    intro id ne1 ne2
    have rawLocals := RootEntryFrame.raw_locals machine (CurrentCallArguments.destination place) (CallEntryFacts.freshRoot before).2
    have initial : (CurrentCallReferenceEntry.copiedFrame options remaining span prepared.frame 1 (prepared.valid i1) argument len).locals[id.val]? =
        some (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
      simp only [CurrentCallReferenceEntry.copiedFrame,prepared,firstLive,firstCache,RootFrameData.live,RootFrameData.write,
        RootFrameData.cache,RootFrameData.atSpan,LocalOperands.cachedLayoutFrame,Array.getElem?_set,i1,Ne.symm ne1,ite_false]
      change initialRoot.frame.locals[id.val]? = _
      rw [show initialRoot.frame.locals = Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout) from rawLocals]
      simp [id.isLt]
    have found := argument_slot source validCopied firstDone frameEq count id.val _ ne1 ne2 initial
    have valueEq := Option.some.inj ((Array.getElem?_eq_getElem (argsRoot.valid id)).symm.trans found)
    exact congrArg LocalState.value valueEq
  have finish := RootEntryFinish.actual_finish options limits (remaining+1) span frames protectedFrame finalMachine
    argsRoot.body argsRoot.size (dead ⟨0,by decide⟩ (by decide) (by decide)) (dead ⟨6,by decide⟩ (by decide) (by decide))
    (dead ⟨13,by decide⟩ (by decide) (by decide)) (dead ⟨14,by decide⟩ (by decide) (by decide)) argsRoot.noClocks
  have tail := tail_of_steps options limits (remaining+1) span frames argsRoot (CurrentCallBoolWindow.after source) place _ _ protect finish
  change (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
      (RootCallCore.argumentBody (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
        (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base argument len) (second count))
      (Storage.withCurrent frames initialRoot.frame machine) =
      .ok (2,2) (Storage.withCurrent frames argsRoot.frame (CurrentCallBoolWindow.after source)) at arguments
  have push := CurrentCallPush.push options (remaining+1) span limits input.machine.settings.debugOff before frames (CurrentCallArguments.destination place) stackReady
  have rawEq : CallEntryFacts.rawPushedState frames before (CurrentCallArguments.destination place) =
      Storage.withCurrent frames initialRoot.frame machine := rfl
  change (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).pushRaw ()
      RootBody.reflected.functionInstance RootBody.reflected.body (.memory place) (.stop true) (⟨⟨frames⟩,before⟩ : RootState) =
      .ok () (CallEntryFacts.rawPushedState frames before (.memory place)) at push
  change CallEntryFacts.rawPushedState frames before (.memory place) = Storage.withCurrent frames initialRoot.frame machine at rawEq
  have getFrame := CallEntryLocals.get_frame options limits (remaining+1) span frames initialRoot.frame machine
  have setFrame := CallEntryLocals.set_frame options limits (remaining+1) span frames initialRoot.frame initialRoot.frame machine
  have preamble : initialRoot.frame.location = .unwinding ⟨559⟩ := rfl
  have trackNone : initialRoot.frame.trackCallerArg = none := rfl
  have unchanged : {initialRoot.frame with trackCallerArg := none} = initialRoot.frame := by rw [←trackNone]
  refine ⟨ctx,source,validCopied,firstDone,borrowed,physical,room,updated,frameEq,?_,?_,written,extra,sourceBinding,readyAfter,initialized,snapshot,idEq,pointerEq,offsetEq,mutation⟩
  · change Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base argument len),.Copy (second count)]
        false (.memory place) (.stop true) (⟨⟨frames⟩,before⟩ : RootState) = _
    rw [RootCallCore.actual_entry_eq]
    unfold RootCallCore.core
    simp only [bind,EStateM.bind]
    rw [push,rawEq]
    dsimp only
    rw [getFrame]
    simp only [EStateM.bind,preamble,pure,EStateM.pure]
    simp only [preamble] at unchanged
    rw [unchanged,setFrame]
    dsimp only
    rw [arguments]
    dsimp only
    exact tail
  · exact returnEq

/-- The source-copy frame is constructed by actual entry, before its retag. -/
def sourceInputFrame {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frames : Array CompilerFrameContext.ActualFrame) : CompilerFrameContext.ActualFrame :=
  let prepared := firstLive (root before frames place input.machine.settings.noDataRace)
  CurrentCallReferenceEntry.copiedFrame options remaining span prepared.frame 1 (prepared.valid i1) argument len

/-- Existing entry witnesses, packaged only as output data for the body. -/
structure Output {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frames : Array CompilerFrameContext.ActualFrame) where
  ctx : ActualReferenceContext.Context options remaining span
  source : CurrentCallReferenceEntry.ViewedOutcome options remaining span ctx (CurrentCallPush.preparedMachine before frames)
    tracker frames (sourceInputFrame input frames) {} argument len place call data .FnEntry true
  validCopied : 1 < (sourceInputFrame input frames).locals.size
  firstDone : RootFrame
  borrowed : CurrentCallBoolProtection.Borrowed source.base.raw
  physical : CandidateCurrentBoolUninitWrite.PhysicalWindow (CurrentCallBoolWindow.after source) place
  room : source.base.raw.output.global.nextPointerTag.value < 18446744073709551615
  updated : Allocation Provenance BorrowTree

namespace Output
variable {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {frames : Array CompilerFrameContext.ActualFrame}

def protectedFrame (out : Output input frames) (count : UInt64) : CompilerFrameContext.ActualFrame :=
  TypedBorrowSteps.registeredFrame (atSpan (RootArgumentsTwo.result out.firstDone count) ⟨601⟩).frame
    out.source.base.raw.output.frame out.physical.id out.source.base.raw.output.global.nextPointerTag

def retagged (out : Output input frames) (count : UInt64) : RootState :=
  ReturnProtection.borrowedState frames (atSpan (RootArgumentsTwo.result out.firstDone count) ⟨601⟩).frame
    out.source.base.raw.output.frame (CurrentCallBoolWindow.after out.source)
    ⟨out.source.base.raw.output.global,tracker.retagMode⟩ out.room out.physical.id out.physical.entry out.borrowed.output.child.tree

def machine (out : Output input frames) (count : UInt64) : Before :=
  {(out.retagged count).machine with memory := {(out.retagged count).machine.memory with live :=
    (((out.retagged count).machine.memory.live.filter fun row => row.1 != out.physical.id).push
      (out.physical.id,{out.physical.entry with allocation := out.updated}))}}

def frame (out : Output input frames) (count : UInt64) : CompilerFrameContext.ActualFrame :=
  CallEntryFacts.doneRootFrame {out.protectedFrame count with location := .unwinding ⟨559⟩}
end Output

/-- Exact already-proved postentry facts, rather than a new input domain. -/
structure Facts {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {frames : Array CompilerFrameContext.ActualFrame} (out : Output input frames) (count : UInt64) : Prop where
  firstFrame : out.firstDone.frame = CurrentCallReferenceEntry.writtenFrame out.source 1 out.validCopied
  actual : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
    RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
    #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base argument len), .Copy (second count)]
    false (CurrentCallArguments.destination place) (.stop true) (⟨⟨frames⟩,before⟩ : RootState) =
    .ok () (Storage.withCurrent frames (out.frame count) (out.machine count))
  destination : (out.frame count).returnPlace = CurrentCallArguments.destination place
  written : CurrentCallBoolProtection.Written out.borrowed
  extra : out.updated.extra = (CurrentCallBoolProtection.writeResult out.borrowed).tree
  sourceWindow : CandidateCallBindings.WindowBinding (out.machine count)
    (CurrentCallTypedFnEntry.changedPointer out.source.base.raw.sourcePointer.value call.sourceId tracker.global.nextPointerTag)
    call.sourceId call.sourceOffset len.toNat
  memoryReady : CurrentCallBoolProtection.ProfileMemoryReadiness (out.machine count) call
  initialized : call.sourceId = call.returnId → InitMaskCopy.InitializedOn out.updated.initializationMask
    (Size.ofBytes (UInt64.ofNat call.sourceOffset)) (Size.ofBytes (UInt64.ofNat call.sourceOffset+len))
  snapshot : AllocationCopy.snapshot out.updated = AllocationCopy.snapshot out.physical.entry.allocation
  returnId : out.physical.id = call.returnId
  returnPointer : out.physical.pointer = out.source.base.raw.returnPointer.value
  returnOffset : out.physical.offset = UInt64.ofNat call.returnOffset
  mutation : Allocation.writeUninit (allocRange (Size.ofBytes out.physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
    ((out.physical.entry.allocation.setExtra out.borrowed.output.child.tree).setExtra
      (CurrentCallBoolProtection.writeResult out.borrowed).tree) = .ok () out.updated

/-- Configuration clauses survive the concrete identity/cache, retag and
physical write updates; this is derived output, not a postentry admission gate. -/
theorem Output.settings {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {frames : Array CompilerFrameContext.ActualFrame} (out : Output input frames) (count : UInt64) :
    DuplicatePrefixCallModel.Model options remaining span (out.machine count) := by
  have default : tracker.retagMode = .Default := by
    obtain ⟨other,enabled,mode⟩ := input.machine.settings.defaultTracker
    have same : other = tracker := Option.some.inj (enabled.symm.trans input.machine.state.enabled)
    simpa only [same] using mode
  have controlEq : (config options (remaining+1) span).terminators.getControl (out.machine count).user =
      (config options (remaining+1) span).terminators.getControl before.user := by
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  exact { input.machine.settings with
    ghostOff := rfl
    shallow := input.machine.settings.shallow
    defaultTracker := ⟨TypedBorrowSteps.registeredTracker
      (ReferenceBorrowDriver.allocatedTracker ⟨out.source.base.raw.output.global,tracker.retagMode⟩ out.room)
      out.source.base.raw.output.global.nextPointerTag, rfl, default⟩
    noDataRace := input.machine.settings.noDataRace
    noBackend := input.machine.settings.noBackend
    metadata := input.machine.settings.metadata
    fixedScheduler := input.machine.settings.fixedScheduler
    unchecked := by rw [controlEq];exact input.machine.settings.unchecked
    noGc := by rw [controlEq];exact input.machine.settings.noGc }

/-- The actual typed retag and physical Bool write preserve the same populated
cache's origin certificate. -/
theorem Output.cacheOrigins {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {frames : Array CompilerFrameContext.ActualFrame} (out : Output input frames) (count : UInt64) :
    DuplicatePrefixTypeCacheOrigins.Origins (out.machine count).user.payload.payload.user.types :=
  out.source.base.cacheOrigins

/-- The actual installed frame reuses the generic structural frame formula;
that formula imposes no allocation identity or provenance restriction. -/
theorem Facts.frame_installed {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {frames : Array CompilerFrameContext.ActualFrame} {out : Output input frames} {count : UInt64}
    (facts : Facts out count) :
    out.frame count = PositiveRootInstalledFrame.installed
      (root before frames place input.machine.settings.noDataRace)
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (CurrentCallTypedFnEntry.changedPointer out.source.base.raw.sourcePointer.value call.sourceId tracker.global.nextPointerTag)
        len ActualReferenceMetadata.reference).imm
      count {} call.sourceId tracker.global.nextPointerTag out.physical.id out.source.base.raw.output.global.nextPointerTag := by
  have sourceBorrow : ({} : FrameState).addProtector call.sourceId tracker.global.nextPointerTag = out.source.base.raw.output.frame :=
    Option.some.inj out.source.base.outputFrame
  simp only [Output.frame,Output.protectedFrame,PositiveRootInstalledFrame.installed,
    RootArgumentsTwo.result,RootFrameData.write,RootFrameData.live,RootFrameData.cache,RootFrameData.atSpan,
    LocalOperands.cachedLayoutFrame]
  simp only [facts.firstFrame,CurrentCallReferenceEntry.writtenFrame,sourceInputFrame,CurrentCallReferenceEntry.copiedFrame,
    PositiveRootArguments.firstDone,PositiveRootArguments.protectedRoot,EmptyRootArguments.firstLive,EmptyRootArguments.firstCache,
    RootFrameData.live,RootFrameData.write,RootFrameData.cache,RootFrameData.atSpan,LocalOperands.cachedLayoutFrame,
    TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,i1,i2,Array.set_set,Array.getElem_set_self,sourceBorrow]

/-- The actual source allocation row after Bool protection, with physical
metadata retained on the same allocation as well as on a distinct allocation. -/
theorem Facts.source_allocation {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {frames : Array CompilerFrameContext.ActualFrame} {out : Output input frames} {count : UInt64}
    (facts : Facts out count) (positive : 0 < len.toNat) :
    ∃ entry, (out.machine count).memory.live.find? (fun row => row.1 == call.sourceId) = some (call.sourceId,entry) ∧
      entry.allocation.extra = (if call.sourceId = call.returnId then
        (CurrentCallBoolProtection.writeResult out.borrowed).tree else out.source.base.raw.output.child.tree) ∧
      entry.allocation.byteSize = out.source.base.raw.sourceAllocation.byteSize ∧
      entry.allocation.len = out.source.base.raw.sourceAllocation.len ∧ entry.allocation.mutability = .Mut ∧
      InitMaskCopy.WellFormed entry.allocation.initializationMask ∧
      entry.allocation.initializationMask.len = entry.allocation.byteSize ∧
      (call.sourceId = call.returnId → entry.allocation = out.updated) ∧
      (call.sourceId ≠ call.returnId → entry.allocation = out.source.base.entry.allocation.setExtra out.source.base.raw.output.child.tree) := by
  apply CurrentCallBoolWindow.source_allocation_after_write options limits remaining span out.ctx
    (CurrentCallPush.preparedMachine before frames) tracker argument len place call data
    (CurrentCallPush.prepared_input input frames) frames (sourceInputFrame input frames) {} out.source positive
    out.physical facts.returnId (CurrentCallBoolProtection.writeResult out.borrowed).tree out.updated (out.machine count)
  · simpa only [Allocation.setExtra,Allocation.mapExtra] using facts.mutation
  · exact congrArg (fun memory => memory.live) (MemoryCopyBridge.live_update_twice (CurrentCallBoolWindow.after out.source).memory out.physical.id
      {out.physical.entry with allocation := out.physical.entry.allocation.setExtra out.borrowed.output.child.tree}
      {out.physical.entry with allocation := out.updated})

/-- The existing pure MIR prefix consumes the actual entry output and reaches
its shared-Ref site. No additional frame or machine-validity packet is supplied. -/
theorem until_shared_reference {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {out : Output input #[]} {count : UInt64} (facts : Facts out count) (nonzero : count ≠ 0) :
    ∃ frame, SuccessfulTrace.Trace (config options (remaining+1) span) limits
      (Storage.withCurrent #[] (out.frame count) (out.machine count))
      (Storage.withCurrent #[] frame (RootZeroCompleteState.tick options remaining span (out.machine count))) ∧
      GenericFunctionEntryPrefix.Shape (out.frame count) frame count := by
  let initial := root before #[] place input.machine.settings.noDataRace
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (CurrentCallTypedFnEntry.changedPointer out.source.base.raw.sourcePointer.value call.sourceId tracker.global.nextPointerTag)
    len ActualReferenceMetadata.reference).imm
  have raw : initial.frame.locals = Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout) :=
    RootEntryFrame.raw_locals _ _ _
  have frameEq := facts.frame_installed
  change out.frame count = PositiveRootInstalledFrame.installed initial value count {} call.sourceId
    tracker.global.nextPointerTag out.physical.id out.source.base.raw.output.global.nextPointerTag at frameEq
  have size : (out.frame count).locals.size = 25 := by rw [frameEq];exact PositiveRootInstalledFrame.size _ _ _ _ _ _ _ _
  have cells (i : Fin 25) := PositiveRootInstalledFrame.slot initial raw value count {} call.sourceId
    tracker.global.nextPointerTag out.physical.id out.source.base.raw.output.global.nextPointerTag i
  simp only [←frameEq] at cells
  obtain ⟨body,identity,callee,_,_,_,clocks,_,location⟩ := PositiveRootInstalledFrame.metadata initial value count {}
    call.sourceId tracker.global.nextPointerTag out.physical.id out.source.base.raw.output.global.nextPointerTag
  rw [←frameEq] at body identity callee clocks location
  have immediate : CopyHelperCleanup.AllImmediate (out.frame count) := by
    rw [frameEq]
    exact PositiveRootInstalledFrame.immediate _ raw _ _ _ _ _ _ _
  have model := out.settings count
  obtain ⟨current,enabled,mode⟩ := model.defaultTracker
  let fuel := options.limits.validation-1
  have fuelEq : options.limits.validation = fuel+1 := by
    have configured := input.machine.resources.configuredFuel.2.2.2
    have lower : 64 ≤ DuplicatePrefixCallSpecification.work before len := by
      unfold DuplicatePrefixCallSpecification.work
      omega
    dsimp only [fuel]
    omega
  have unused : ∀ id (valid : id < (out.frame count).locals.size), 7 ≤ id → id ≤ 12 →
      (out.frame count).locals[id]'valid = ⟨.dead,none⟩ := by
    intro id valid low high
    have row := cells ⟨id,by omega⟩
    simp only [show ¬(14=id ∨ 13=id ∨ 6=id ∨ 0=id) by omega,show ¬2=id by omega,
      show ¬1=id by omega,ite_false] at row
    exact row
  exact GenericFunctionEntryPrefix.executes_preserving options limits remaining span
    (DuplicatePrefixCallModel.sourceComparator options remaining span before input.machine.settings)
    model.debugOff fuel fuelEq (out.frame count) (out.machine count) count nonzero size
    (by simpa using congrArg LocalState.value (cells ⟨2,by decide⟩))
    (by simpa using congrArg LocalState.layout (cells ⟨2,by decide⟩))
    (by simpa using congrArg LocalState.value (cells ⟨3,by decide⟩))
    (by simpa using congrArg LocalState.layout (cells ⟨3,by decide⟩))
    (by simpa using congrArg LocalState.value (cells ⟨4,by decide⟩))
    (by simpa using congrArg LocalState.value (cells ⟨5,by decide⟩))
    (by simpa using congrArg LocalState.layout (cells ⟨4,by decide⟩))
    (by simpa using congrArg LocalState.layout (cells ⟨5,by decide⟩)) unused
    (body.trans initial.body) (identity.trans initial.identity) (callee.trans initial.callee) location
    (clocks.trans initial.noClocks) immediate current enabled mode model.ghostOff model.shallow
    model.unchecked model.noGc model.fixedScheduler

/-- Package the full actual entry theorem without adding any hypothesis. -/
theorem complete {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frames : Array CompilerFrameContext.ActualFrame) (stackReady : CurrentCallPush.StackReadiness before frames)
    (memoryReady : CurrentCallBoolProtection.ProfileMemoryReadiness before call)
    (positive : 0 < len.toNat) (count : UInt64) : ∃ out : Output input frames, Facts out count := by
  obtain ⟨ctx,source,validCopied,firstDone,borrowed,physical,room,updated,firstFrame,actual,destination,written,extra,
    sourceWindow,memoryAfter,initialized,snapshot,returnId,returnPointer,returnOffset,mutation⟩ :=
    invoke options limits remaining span before tracker argument len place call data input frames stackReady memoryReady positive count
  exact ⟨⟨ctx,source,validCopied,firstDone,borrowed,physical,room,updated⟩,
    ⟨firstFrame,actual,destination,written,extra,sourceWindow,memoryAfter,initialized,snapshot,returnId,returnPointer,returnOffset,mutation⟩⟩

/-- Full actual entry followed by the actual pure body prefix; all output
certificates used by the continuation are constructed internally. -/
theorem invoke_until_shared_reference {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (stackReady : CurrentCallPush.StackReadiness before #[])
    (memoryReady : CurrentCallBoolProtection.ProfileMemoryReadiness before call)
    (positive : 0 < len.toNat) (count : UInt64) (nonzero : count ≠ 0) :
    ∃ out : Output input #[], Facts out count ∧ ∃ frame,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] (out.frame count) (out.machine count))
        (Storage.withCurrent #[] frame (RootZeroCompleteState.tick options remaining span (out.machine count))) ∧
      GenericFunctionEntryPrefix.Shape (out.frame count) frame count := by
  obtain ⟨out,facts⟩ := complete input #[] stackReady memoryReady positive count
  exact ⟨out,facts,until_shared_reference facts nonzero⟩

end
end DuplicatePrefix.CurrentCallEntry

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallEntry.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved actual full current call entry dependency {dependency}"
