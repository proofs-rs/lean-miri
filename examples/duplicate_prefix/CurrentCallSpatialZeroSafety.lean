import duplicate_prefix.CurrentCallSpatialEntryRelease
import duplicate_prefix.CurrentCallSpatialEntryBoolPhysical
import duplicate_prefix.CurrentCallSpatialEntryFacts
import duplicate_prefix.CurrentCallResourceRootFinish
import duplicate_prefix.DuplicatePrefixArgumentCallResult
import duplicate_prefix.PushThread

namespace DuplicatePrefix.CurrentCallSpatialZeroSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CurrentCallResourceNormalization
open CurrentCallSpatialCover CurrentCallSpatialEntry CanonicalConfigFacts ActualReferenceContext RootFrameData
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

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

variable {options remaining span root before tracker ctx offset len source returnOffset ret place}
    {C : Conditions options remaining span #[] root before tracker ctx offset len source returnOffset ret place}
    {limits} (out : Output C limits 0)

/-- All release, original-pointer access and physical store certificates are
internally derived from the actual spatial entry output. -/
theorem finish (empty : C.borrowFrame={})
    (thread : Miri.Concurrency.ThreadRecord)
    (active : (CurrentCallSpatialEntryFacts.machine out).threads.activeThread?=some thread)
    (rootStop : root.frame.returnContinuation=.stop true)
    (rootDestination : root.frame.returnPlace.toRuntimePlace=⟨.memory place.mplace,place.layout⟩)
    (rootVarargs : root.frame.vaList=#[]) :
    ∃final,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] (CurrentCallSpatialEntryFacts.finishedFrame out) (CurrentCallSpatialEntryFacts.machine out)) final ∧
      ExecutionMachine.step (config options (remaining+1) span) limits () final=(final,.ok false) ∧final.stack.frames=#[] := by
  obtain ⟨data,owner,B,bPointer,bAllocation,bCompletion,⟨released⟩⟩:=CurrentCallSpatialEntryRelease.release out empty
  obtain ⟨window,windowPointer,windowId,windowOffset,windowEntry,windowBinding,windowReady⟩:=CurrentCallSpatialEntryBoolPhysical.current out
  obtain ⟨result,traceBefore,body,identity,callee,size,located,slot0,returnPlace,extra,continuation,varargs,immediate⟩:=
    CurrentCallSpatialEntryFacts.before_zero_return out rfl
  let machine:=CurrentCallSpatialEntryFacts.machine out
  let current : MachineHooks.BorrowState:=CurrentCallSpatialEntryCurrent.held out
  let beforeReturn:=RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span machine)
  have memory : beforeReturn.memory=machine.memory:=by
    unfold beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators] <;> rfl
  have addresses : beforeReturn.user.addresses=machine.user.addresses:=by
    unfold beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators] <;> rfl
  have extras : beforeReturn.user.payload.payload.user.runtime.extras=machine.user.payload.payload.user.runtime.extras:=by
    unfold beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators] <;> rfl
  have enabled : beforeReturn.borrowTracker=some current:=by
    unfold beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact CurrentCallSpatialEntryFacts.finalTracked out
  have activeNow : beforeReturn.threads.activeThread?=some thread:=by
    unfold beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact active
  have present : Present (ActualWorld beforeReturn) out.physical.id B.allocation:=by
    unfold Present ActualWorld
    rw [memory]
    exact B.present
  let afterB : UniformWindow beforeReturn current data owner out.physical.id out.physical.offset.toNat 1 .ret := {B with
    present:=present
    issued:=CurrentCallAllocationLicense.spatial B.issued beforeReturn current B.allocation present rfl rfl rfl rfl
      (by intro position root found;exact found) (by intro index node found;exact ⟨node,found,rfl,rfl,rfl,rfl⟩)
      B.precise.completion (by intro root origin edge;exact edge)}
  obtain ⟨physical,pointerEq,idEq,offsetEq,entryEq,binding⟩:=CurrentCallRootPhysicalWindow.view (final:=beforeReturn)
    window windowBinding addresses (congrArg MemoryState.live memory)
  have physId : physical.id=out.physical.id:=idEq.trans (windowId.trans (CurrentCallSpatialEntryBoolPhysical.id_eq out).symm)
  have physOffset : physical.offset=out.physical.offset:=offsetEq.trans (windowOffset.trans (CurrentCallSpatialEntryBoolPhysical.offset_eq out).symm)
  have physEntry : physical.entry={out.physical.entry with allocation:=out.updated}:=entryEq.trans windowEntry
  have samePointer : physical.pointer=(CurrentCallSpatialEntryBoolCurrent.parent out).pointer.value:=
    pointerEq.trans (windowPointer.trans (C.returnPointer.trans (CurrentCallSpatialEntryBoolCurrent.original_pointer out).symm))
  let frame:=CurrentCallSpatialEntryRelease.borrowFrame out
  let oldParent:=(CurrentCallSpatialEntryBoolCurrent.parent out).pointer
  have parentIssued : SpatialDelegation beforeReturn current out.physical.id B.allocation B.precise.completion oldParent.grant := by
    have old:=CurrentCallSpatialEntryBoolCurrent.parent_issued out
    rw [←bAllocation,←bCompletion] at old
    exact CurrentCallAllocationLicense.spatial old beforeReturn current B.allocation present rfl rfl rfl rfl
      (by intro position root found;exact found) (by intro index node found;exact ⟨node,found,rfl,rfl,rfl,rfl⟩)
      B.precise.completion (by intro root origin edge;exact edge)
  have parentBinding : PointerBinds B.allocation oldParent:=by rw [bAllocation];exact CurrentCallSpatialEntryBoolCurrent.parent_binding out
  let R : CurrentCallResourceCurrentRelease.Released afterB frame oldParent.grant physical.offset physical.entry := {
    memory:=released.memory,tree:=released.tree
    plan:=by rw [memory];exact released.plan
    live:=by rw [physEntry];exact released.live
    runtime:=released.runtime,parents:=released.parents,shape:=released.shape,capacity:=released.capacity
    distinct:=released.distinct,short:=released.short
    owned:=by rw [physOffset];exact released.owned}
  have model:=tick_model options remaining span _ (tick_model options remaining span _ (CurrentCallSpatialEntryFacts.model out))
  have frameTracked : result.extra.borrowTracker=some frame:=by
    rw [extra]
    exact (CurrentCallSpatialEntryFacts.metadata out).2.2.2.2.2.2.2.1
  have metadata:=CurrentCallSpatialEntryFacts.metadata out
  have noClocks : result.extra.dataRace=none:=by rw [extra];exact metadata.2.2.2.2.2.2.1.trans root.noClocks
  have stop : result.returnContinuation=.stop true:=continuation.trans (metadata.2.2.2.1.trans rootStop)
  have destination : result.returnPlace.toRuntimePlace=⟨.memory place.mplace,place.layout⟩:=by rw [returnPlace,metadata.2.2.2.2.1];exact rootDestination
  have va : result.vaList=#[]:=varargs.trans (metadata.2.2.2.2.2.1.trans rootVarargs)
  have ready : CurrentCallBoolProtection.WindowReady beforeReturn physical.id physical.offset.toNat 1:=by
    rw [idEq,offsetEq]
    exact windowReady.transport extras
  obtain ⟨final,returned,terminal,emptyStack⟩:=CurrentCallResourceRootFinish.finish options limits remaining span place
    (CurrentCallSpatialEntryBoolCurrent.parent out) afterB physical binding physId (congrArg UInt64.toNat physOffset)
    samePointer parentIssued parentBinding result frame R model enabled frameTracked thread activeNow body located size noClocks stop va immediate
    true slot0 destination ready C.validationFuel C.validationEq
  exact ⟨final,SuccessfulTrace.append traceBefore returned,terminal,emptyStack⟩

/-- Positive LIVE spatial source/return resources prove the ORIGINAL count-zero
call Result. Every operation, release Plan, access and scalar store is derived
internally; no whole-source origin or future-success premise is consumed. -/
theorem invoke {options remaining span before tracker ctx offset len source returnOffset ret place}
    (limits : ExecutionMachine.Limits) (race : before.dataRace=none)
    (C : Conditions options remaining span #[] (CurrentCallSpatialEntryControl.root before #[] place race)
      before tracker ctx offset len source returnOffset ret place)
    (stackReady : CurrentCallPush.StackReadiness before #[]) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer source.family.value) len 0 place := by
  obtain ⟨out,actualEntry⟩:=CurrentCallSpatialEntry.invoke limits race C stackReady 0
  let prepared:=CurrentCallSpatialEntry.prepared C
  have rawBorrow:=RootEntryFrame.raw_borrow (CurrentCallPush.preparedMachine before #[]) (.memory place)
    (CallEntryFacts.freshRoot before).2 tracker C.state.enabled
  have empty : prepared.borrowFrame={} := Option.some.inj (C.frameBorrow.symm.trans rawBorrow)
  obtain ⟨oldThread,oldActive,_⟩:=stackReady
  let thread:={oldThread with topUserRelevantFrame:=some 0}
  have active : (CurrentCallSpatialEntryFacts.machine out).threads.activeThread?=some thread:=by
    rw [CurrentCallSpatialEntryFacts.threads_eq out]
    exact PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 oldThread 0 oldActive
  obtain ⟨final,trace,terminal,emptyStack⟩:=finish out empty thread active rfl rfl rfl
  let cfg:=config options (remaining+1) span
  let installed:=Storage.withCurrent #[] (CurrentCallSpatialEntryFacts.finishedFrame out) (CurrentCallSpatialEntryFacts.machine out)
  let context : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit:=⟨cfg,limits,fun _ _=>True⟩
  have entry : CallSafety.IsCallEntry 1 installed:=⟨by decide,rfl⟩
  have past : CallSafety.pastCallBoundary 1 final:=by change final.stack.frames.size<1;rw [emptyStack];decide
  exact ⟨installed,final,actualEntry,trace,terminal,emptyStack,
    SuccessfulTrace.no_errors context 1 installed final entry trace past,
    SuccessfulTrace.no_ub context 1 installed final entry trace past,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

end
end DuplicatePrefix.CurrentCallSpatialZeroSafety
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallSpatialZeroSafety.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved spatial zero safety dependency {dependency}"
