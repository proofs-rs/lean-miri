import duplicate_prefix.CurrentCallCheckpointZeroControl
import duplicate_prefix.CurrentCallCheckpointRootRelease
import duplicate_prefix.CurrentCallSpatialControlView
import duplicate_prefix.CurrentCallResourceRootFinish

namespace DuplicatePrefix.CurrentCallCheckpointZeroFinish
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallPostEntryCheckpoint CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

private def window_world {before after tracker data owner id offset length mode}
    (old : UniformWindow before tracker data owner id offset length mode) (world : ActualWorld after=ActualWorld before) :
    UniformWindow after tracker data owner id offset length mode where
  loan:=old.loan;pointer:=old.pointer;allocation:=old.allocation;precise:=old.precise
  loanAt:=old.loanAt;pointerAt:=old.pointerAt;pointerId:=old.pointerId
  present:=by rw [world];exact old.present
  preciseAt:=old.preciseAt
  binding:=old.binding
  issued:=CurrentCallSpatialControlView.issued old.issued world
  parents:=old.parents
  window:=old.window

private theorem tick_model (options remaining span before)
    (model : DuplicatePrefixCallModel.Model options remaining span before) :
    DuplicatePrefixCallModel.Model options remaining span (RootZeroCompleteState.tick options remaining span before):=by
  have flags:=RootZeroCompleteState.tick_flags options remaining span before
  have unchecked:=model.unchecked
  have noGc:=model.noGc
  rw [(actual_fields options () (remaining+1) span).terminators] at unchecked noGc
  unfold RootZeroCompleteState.tick SourceControl.accounted at flags ⊢
  rw [(actual_fields options () (remaining+1) span).terminators] at flags ⊢
  exact {model with
    unchecked:=by rw [(actual_fields options () (remaining+1) span).terminators];exact flags.1.trans unchecked
    noGc:=by rw [(actual_fields options () (remaining+1) span).terminators];exact flags.2.trans noGc}

/-- Common zero-count body completion through both actual root releases and
the validated store to the original destination. No initial source/Bool W is
reconstructed, and no uniform source completion is needed. -/
theorem invoke {options remaining span len place}
    (checkpoint : Checkpoint options remaining span len 0 place) (limits : ExecutionMachine.Limits) :
    ∃final,SuccessfulTrace.Trace (config options (remaining+1) span) limits
      (Storage.withCurrent #[] checkpoint.frame checkpoint.machine) final ∧
      ExecutionMachine.step (config options (remaining+1) span) limits () final=(final,.ok false) ∧final.stack.frames=#[]:=by
  obtain ⟨frame,trace,body,identity,callee,extra,destination,continuation,varargs,localsIdentity,size,location,slot0,immediate⟩:=
    CurrentCallCheckpointZeroControl.invoke checkpoint limits
  obtain ⟨released⟩:=CurrentCallCheckpointRootRelease.release checkpoint
  let beforeReturn:=RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span checkpoint.machine)
  have world : ActualWorld beforeReturn=ActualWorld checkpoint.machine:=rfl
  let B:=window_world checkpoint.output.window world
  have addresses : beforeReturn.user.addresses=checkpoint.machine.user.addresses:=by
    unfold beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    rfl
  let physical : CurrentCallBoolScalarWrite.Window beforeReturn place:={checkpoint.output.physical with
    live:=by change checkpoint.machine.memory.live.find? _=_;exact checkpoint.output.physical.live
    cachedBase:=by rw [addresses];exact checkpoint.output.physical.cachedBase}
  have binding : CandidateCallBindings.WindowBinding beforeReturn physical.pointer physical.id physical.offset.toNat 1:=by
    obtain ⟨entry,base,live,cached,storage,room,bounds,address,nonnull,provenance⟩:=checkpoint.output.binding
    refine ⟨entry,base,?_,?_,storage,room,?_,?_,nonnull,?_⟩
    · change checkpoint.machine.memory.live.find? (fun row=>row.1==checkpoint.output.physical.id)=some (checkpoint.output.physical.id,entry)
      simpa only [checkpoint.output.physicalId] using live
    · rw [addresses]
      simpa only [physical,checkpoint.output.physicalId] using cached
    · simpa only [physical,checkpoint.output.physicalOffset] using bounds
    · simpa only [physical,checkpoint.output.physicalOffset] using address
    · cases value : checkpoint.output.physical.pointer.provenance with
      | concrete id tag => simpa only [physical,value,checkpoint.output.physicalId] using provenance
      | wildcard =>
        change beforeReturn.user.addresses.provenanceMode≠.strict ∧beforeReturn.user.addresses.exposed.contains physical.id=true ∧_
        rw [addresses]
        simpa only [physical,value,checkpoint.output.physicalId] using provenance
  have issued : SpatialDelegation beforeReturn checkpoint.tracker checkpoint.output.id B.allocation B.precise.completion checkpoint.output.original.grant:=
    CurrentCallSpatialControlView.issued checkpoint.output.originalIssued world
  have model:=tick_model options remaining span _ (tick_model options remaining span _ checkpoint.model)
  have ready : CurrentCallBoolProtection.WindowReady beforeReturn physical.id physical.offset.toNat 1:=by
    change CurrentCallBoolProtection.WindowReady beforeReturn checkpoint.output.physical.id checkpoint.output.physical.offset.toNat 1
    rw [checkpoint.output.physicalId,checkpoint.output.physicalOffset]
    apply checkpoint.output.profile.transport
    unfold beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    rfl
  have currentReleased : CurrentCallResourceCurrentRelease.Released B checkpoint.borrowFrame checkpoint.output.original.grant physical.offset physical.entry:={
    memory:=released.memory,tree:=released.tree,plan:=released.plan,live:=released.live,runtime:=released.runtime,
    parents:=released.parents,shape:=released.shape,capacity:=released.capacity,distinct:=released.distinct,short:=released.short,owned:=released.owned}
  obtain ⟨final,finish,terminal,empty⟩:=CurrentCallResourceRootFinish.finish_pointer options limits remaining span place
    checkpoint.output.original checkpoint.output.originalId B physical binding checkpoint.output.physicalId checkpoint.output.physicalOffset
    checkpoint.output.originalPointer.symm issued checkpoint.output.originalBinding frame checkpoint.borrowFrame currentReleased model checkpoint.tracked
    (by rw [extra];exact checkpoint.frameTracked) checkpoint.thread checkpoint.active (body.trans checkpoint.body) location size
    (by rw [extra];exact checkpoint.noClocks) (continuation.trans checkpoint.stop) (varargs.trans checkpoint.varargs) immediate true slot0
    (by rw [destination];exact checkpoint.destination) ready checkpoint.validationFuel checkpoint.validationEq
  exact ⟨final,SuccessfulTrace.append trace finish,terminal,empty⟩

end
end DuplicatePrefix.CurrentCallCheckpointZeroFinish
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointZeroFinish" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved common zero completion dependency {dependency}"
