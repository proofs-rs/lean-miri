import duplicate_prefix.CurrentCallCheckpointAcceptedControl
import duplicate_prefix.CurrentCallResourceAsMutCall
import duplicate_prefix.CurrentCallSpatialDefaultMutable
namespace DuplicatePrefix.CurrentCallCheckpointDefaultControl
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows CandidateStableCallOwnership CandidateCurrentJointCall
open CurrentCallSpatialCover CurrentCallResourceNormalization
open CurrentCallPostEntryCheckpoint CurrentCallCheckpointRoot3 CanonicalConfigFacts ActualReferenceContext RootReferenceInfo
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
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


private theorem bounds {before tracker ctx mode offset length} (role : RoleCover before tracker ctx mode offset length)
    (positive : 0<length) : offset+length≤role.backing.allocation.extra.locations.size.bytes.toNat:=by
  let byte:=(role.backing.id,offset+length-1)
  have hit : Window role.backing.id offset length byte:=⟨rfl,by dsimp only [byte];omega,by dsimp only [byte];omega⟩
  obtain ⟨i,inside⟩:=role.covered byte hit
  have bound:=((role.roles i ⟨byte,hit,inside⟩).available byte hit inside).1
  have cap:=(role.roles i ⟨byte,hit,inside⟩).issued.capability
  rw [cap.treeExtent,←cap.extent]
  dsimp only [byte] at bound
  omega

private theorem capacity {before tracker ctx mode offset length} (role : RoleCover before tracker ctx mode offset length)
    (positive : 0<length) : role.backing.allocation.extra.locations.size=role.backing.allocation.byteSize := by
  let byte := (role.backing.id,offset)
  have hit : Window role.backing.id offset length byte := ⟨rfl,by simp [byte],by dsimp only [byte];omega⟩
  obtain ⟨i,inside⟩:=role.covered byte hit
  exact (role.roles i ⟨byte,hit,inside⟩).issued.capability.treeExtent

private theorem model_transport {options remaining span} (before after : Before)
    (model : DuplicatePrefixCallModel.Model options remaining span before)
    (user : after.user=before.user) (threads : after.threads=before.threads) (race : after.dataRace=before.dataRace)
    (defaultTracker : ∃tracker,after.borrowTracker=some tracker ∧tracker.retagMode=.Default) :
    DuplicatePrefixCallModel.Model options remaining span after:=by
  exact {model with
    ghostOff:=by rw [user];exact model.ghostOff
    shallow:=by rw [user];exact model.shallow
    defaultTracker:=defaultTracker
    noDataRace:=race.trans model.noDataRace
    noBackend:=by rw [user];exact model.noBackend
    metadata:=by rw [user];exact model.metadata
    fixedScheduler:=by rw [threads];exact model.fixedScheduler
    unchecked:=by rw [user];exact model.unchecked
    noGc:=by rw [user];exact model.noGc}

variable {options remaining span len count place limits}
  {checkpoint : Checkpoint options remaining span len count place} (out : Output checkpoint limits)

def entry (_out : Output checkpoint limits) : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
  {CurrentCallCheckpointLenControl.entry checkpoint with allocation:=
    (CurrentCallCheckpointLenControl.entry checkpoint).allocation.setExtra (CurrentCallCheckpointLenControl.releasedTree checkpoint)}

theorem room : out.tracker.global.nextPointerTag.value<18446744073709551615 := by
  have bound:=out.source.tags
  change out.tracker.global.nextPointerTag.value.toNat+4<18446744073709551615 at bound
  exact UInt64.lt_iff_toNat_lt.mpr (by change _<18446744073709551615;omega)

def tree := (GeneralBorrowRawDefaultExpression.child (entry out).allocation.extra out.tracker.global.protectedTags
  checkpoint.source.tag out.tracker.global.nextPointerTag (UInt64.ofNat checkpoint.offset) len .VisitChildrenOfAccessed).tree

def machine := {ReferenceBorrowDriver.allocatedMachine (CurrentCallCheckpointAcceptedControl.before out) out.tracker (room out) with
  memory:=RetagEntry.updatedMemory (CurrentCallCheckpointAcceptedControl.before out).memory out.source.role.backing.id (entry out) (tree out)}

def afterFrame (input : CurrentCallCheckpointAcceptedControl.Input out) (base : UInt64) :=
  CopyHelperSteps.advance (ActualLocalCopy.written input.frame (RootReferenceFacts.destination false) (layout false)
    (by rw [input.size];decide) (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete out.source.role.backing.id out.tracker.global.nextPointerTag)
        (Size.ofBytes (base+UInt64.ofNat checkpoint.offset))) len (layout false)).imm) (RootReferenceFacts.location false)

/-- Internal execution seam. The common logical P producer supplies these
same-operation certificates; the public continuation derives them internally. -/
theorem statement (input : CurrentCallCheckpointAcceptedControl.Input out)
    (readDone : (GeneralBorrowRawDefaultExpression.read (entry out).allocation.extra out.tracker.global.protectedTags
      checkpoint.source.tag (UInt64.ofNat checkpoint.offset) len .VisitChildrenOfAccessed).status=.Completed)
    (childDone : (GeneralBorrowRawDefaultExpression.child (entry out).allocation.extra out.tracker.global.protectedTags
      checkpoint.source.tag out.tracker.global.nextPointerTag (UInt64.ofNat checkpoint.offset) len .VisitChildrenOfAccessed).outcome=.ok ()) :
    ∃base,(CurrentCallCheckpointAcceptedControl.before out).user.addresses.baseAddr.find?
      (fun row=>row.allocId==out.source.role.backing.id)=some ⟨out.source.role.backing.id,base⟩ ∧
      out.source.role.family.value=Pointer.new (.concrete out.source.role.backing.id checkpoint.source.tag)
        (Size.ofBytes (base+UInt64.ofNat checkpoint.offset)) ∧
      base+UInt64.ofNat checkpoint.offset≠0 ∧ExecutionMachine.step (config options (remaining+1) span) limits ()
      (Storage.withCurrent #[] input.frame (CurrentCallCheckpointAcceptedControl.before out))=
      (Storage.withCurrent #[] (afterFrame out input base) (machine out),.ok true) := by
  obtain ⟨base,cached,pointer,nonnull⟩:=CurrentCallCheckpointAcceptedControl.source_address out
  have model:=tick_model options remaining span _ (tick_model options remaining span _ out.model)
  have currentAllocation : out.source.role.backing.allocation=(entry out).allocation:=out.source.allocation
  have family : out.source.role.family.value=checkpoint.source.role.family.value:=congrArg (fun family=>family.value) out.source.family
  have valid1 : (1:MIR.LocalId)<input.frame.locals.size:=by rw [input.size];decide
  have valid16 : RootReferenceFacts.destination false<input.frame.locals.size:=by rw [input.size];decide
  have sourceStored:=Option.some.inj ((Array.getElem?_eq_getElem valid1).symm.trans input.source)
  have destStored:=Option.some.inj ((Array.getElem?_eq_getElem valid16).symm.trans input.dest16)
  have baseEq : (config options remaining span).access.runtime.base=(config options (remaining+1) span).access.runtime.base:=by
    rw [actual_access_runtime,actual_access_runtime]
  have sourceLive : input.frame.locals[1].value=.live (.immediate (RetagReferencePlace.sliceValue
    (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete out.source.role.backing.id checkpoint.source.tag) (Size.ofBytes (base+UInt64.ofNat checkpoint.offset)))
      len ActualReferenceMetadata.reference).imm):=by
    rw [←family,pointer,baseEq] at sourceStored
    exact congrArg LocalState.value sourceStored
  have enabled : (CurrentCallCheckpointAcceptedControl.before out).borrowTracker=some out.tracker:=out.tracked
  have mode : out.tracker.retagMode=.Default:=by
    obtain ⟨actual,tracked,mode⟩:=out.model.defaultTracker
    have same:=Option.some.inj (tracked.symm.trans out.tracked)
    subst actual
    exact mode
  have live : (CurrentCallCheckpointAcceptedControl.before out).memory.live.find? (fun row=>row.1==out.source.role.backing.id)=
      some (out.source.role.backing.id,entry out):=by
    rw [out.source.id]
    exact out.result.sourceLive
  have origins : DuplicatePrefixTypeCacheOrigins.Origins
    (CurrentCallCheckpointAcceptedControl.before out).user.payload.payload.user.types:=by
    unfold CurrentCallCheckpointAcceptedControl.before RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact out.origins
  have positive : (0:UInt64)<len := UInt64.lt_iff_toNat_lt.mpr checkpoint.source.positive
  have startEq : (UInt64.ofNat checkpoint.offset).toNat=checkpoint.offset:=by
    have small:=out.source.role.family.value.offset.bytes.toNat_lt
    obtain ⟨a,b,c,d,e,f,g,h,i,j⟩:=out.source.binding
    have fits : checkpoint.offset<2^64:=by omega
    exact Nat.mod_eq_of_lt fits
  have requestBounds : (UInt64.ofNat checkpoint.offset).toNat+len.toNat≤(entry out).allocation.extra.locations.size.bytes.toNat:=by
    rw [startEq,←currentAllocation]
    exact bounds out.source.role checkpoint.source.positive
  have run:=CurrentCallResourceAsMutCall.default_statement options limits remaining span model.preciseOff model.implicitOff model.debugOff
    model.nullComparator
    checkpoint.dynamicFuel checkpoint.validationFuel checkpoint.dynamicEq checkpoint.validationEq
    base (UInt64.ofNat checkpoint.offset) len out.source.role.backing.id (entry out) positive nonnull checkpoint.source.signedFits
    #[] input.frame (CurrentCallCheckpointAcceptedControl.before out) input.body input.identity input.callee input.location
    out.tracker enabled mode (room out) checkpoint.source.tag requestBounds readDone childDone
    (by rw [←currentAllocation];exact capacity out.source.role checkpoint.source.positive)
    valid1 valid16 sourceLive (congrArg LocalState.layout sourceStored) (congrArg LocalState.value destStored) (congrArg LocalState.layout destStored)
    input.clocks model.ghostOff model.shallow cached live model.noDataRace model.metadata origins
  exact ⟨base,cached,pointer,nonnull,run⟩

/-- The common Default-mut statement derives both retag certificates from the fixed spatial source bank. -/
theorem invoke (input : CurrentCallCheckpointAcceptedControl.Input out) :
    ∃base,(CurrentCallCheckpointAcceptedControl.before out).user.addresses.baseAddr.find?
      (fun row=>row.allocId==out.source.role.backing.id)=some ⟨out.source.role.backing.id,base⟩ ∧
      out.source.role.family.value=Pointer.new (.concrete out.source.role.backing.id checkpoint.source.tag)
        (Size.ofBytes (base+UInt64.ofNat checkpoint.offset)) ∧
      base+UInt64.ofNat checkpoint.offset≠0 ∧ExecutionMachine.step (config options (remaining+1) span) limits ()
      (Storage.withCurrent #[] input.frame (CurrentCallCheckpointAcceptedControl.before out))=
      (Storage.withCurrent #[] (afterFrame out input base) (machine out),.ok true) := by
  have startEq : (UInt64.ofNat checkpoint.offset).toNat=checkpoint.offset:=by
    obtain ⟨a,b,c,d,e,f,g,h,i,j⟩:=out.source.binding
    have small:=out.source.role.family.value.offset.bytes.toNat_lt
    exact Nat.mod_eq_of_lt (by omega)
  have requestBounds : (UInt64.ofNat checkpoint.offset).toNat+len.toNat≤out.source.role.backing.allocation.extra.locations.size.bytes.toNat:=by
    rw [startEq]
    exact bounds out.source.role checkpoint.source.positive
  have nonzero : len≠0:=by
    intro zero
    have positive:=checkpoint.source.positive
    rw [zero] at positive
    contradiction
  have short : out.source.role.backing.allocation.extra.nodes.size<65536:=by have n:=out.source.nodes;omega
  have nodeRoom : out.source.role.backing.allocation.extra.nodes.size+1≤4294967295:=by have n:=out.source.nodes;omega
  obtain ⟨parent,node,mapped,present,tag,readDone,childDone,rest⟩ :=
    CurrentCallSpatialDefaultMutable.construct out.source.role out.source.runtime out.source.distinct short nodeRoom
      checkpoint.source.tag out.source.concrete (room out) (UInt64.ofNat checkpoint.offset) len startEq rfl nonzero requestBounds
  have currentAllocation : out.source.role.backing.allocation=(entry out).allocation:=out.source.allocation
  change (GeneralBorrowRawDefaultExpression.read out.source.role.backing.allocation.extra out.tracker.global.protectedTags
    checkpoint.source.tag (UInt64.ofNat checkpoint.offset) len .VisitChildrenOfAccessed).status=.Completed at readDone
  rw [currentAllocation] at readDone childDone
  exact statement out input readDone childDone


structure Done where
  input : CurrentCallCheckpointAcceptedControl.Input out
  base : UInt64
  cached : (CurrentCallCheckpointAcceptedControl.before out).user.addresses.baseAddr.find?
    (fun row=>row.allocId==out.source.role.backing.id)=some ⟨out.source.role.backing.id,base⟩
  pointer : out.source.role.family.value=Pointer.new (.concrete out.source.role.backing.id checkpoint.source.tag)
    (Size.ofBytes (base+UInt64.ofNat checkpoint.offset))
  nonnull : base+UInt64.ofNat checkpoint.offset≠0
  step : ExecutionMachine.step (config options (remaining+1) span) limits ()
    (Storage.withCurrent #[] input.frame (CurrentCallCheckpointAcceptedControl.before out))=
    (Storage.withCurrent #[] (afterFrame out input base) (machine out),.ok true)


def tracker := ReferenceBorrowDriver.allocatedTracker out.tracker (room out)


theorem counter : (tracker out).global.nextPointerTag.value.toNat=out.tracker.global.nextPointerTag.value.toNat+1 :=
  GenericFunctionEntryNumerics.successor_value out.tracker.global.nextPointerTag (room out)

theorem tag_margin : (tracker out).global.nextPointerTag.value.toNat+3<18446744073709551615:=by
  have old:=out.source.tags
  change out.tracker.global.nextPointerTag.value.toNat+4<18446744073709551615 at old
  rw [counter out]
  omega

theorem fresh : (tracker out).global.nextPointerTag.value<18446744073709551615:=by
  have small:=tag_margin out
  exact UInt64.lt_iff_toNat_lt.mpr (by change _<18446744073709551615;omega)

theorem tracked : (machine out).borrowTracker=some (tracker out):=rfl

theorem mode : (tracker out).retagMode=.Default:=by
  obtain ⟨actual,known,mode⟩:=out.model.defaultTracker
  have same:=Option.some.inj (known.symm.trans out.tracked)
  subst actual
  exact mode

theorem model : DuplicatePrefixCallModel.Model options remaining span (machine out):=by
  have beforeModel:=tick_model options remaining span _ (tick_model options remaining span _ out.model)
  exact model_transport _ _ beforeModel rfl rfl rfl ⟨tracker out,tracked out,mode out⟩

theorem addresses : (machine out).user.addresses=out.machine.user.addresses:=by
  unfold machine CurrentCallCheckpointAcceptedControl.before ReferenceBorrowDriver.allocatedMachine RootZeroCompleteState.tick SourceControl.accounted
  rw [(actual_fields options () (remaining+1) span).terminators]
  rfl

theorem types : (machine out).user.payload.payload.user.types=out.machine.user.payload.payload.user.types:=by
  unfold machine CurrentCallCheckpointAcceptedControl.before ReferenceBorrowDriver.allocatedMachine RootZeroCompleteState.tick SourceControl.accounted
  rw [(actual_fields options () (remaining+1) span).terminators]
  rfl

theorem extras : (machine out).user.payload.payload.user.runtime.extras=out.machine.user.payload.payload.user.runtime.extras:=by
  unfold machine CurrentCallCheckpointAcceptedControl.before ReferenceBorrowDriver.allocatedMachine RootZeroCompleteState.tick SourceControl.accounted
  rw [(actual_fields options () (remaining+1) span).terminators]
  rfl

theorem origins : DuplicatePrefixTypeCacheOrigins.Origins (machine out).user.payload.payload.user.types:=by
  rw [types out]
  exact out.origins

theorem active : ∃thread,(machine out).threads.activeThread?=some thread ∧thread.topUserRelevantFrame=some 0:=out.active

theorem live : (machine out).memory.live.find? (fun row=>row.1==out.source.role.backing.id)=some
    (out.source.role.backing.id,{entry out with allocation:=(entry out).allocation.setExtra (tree out)}):=
  MemoryCopyBridge.live_lookup_replaced _ _ _

private theorem written_slot (frame : CompilerFrameContext.ActualFrame) (localId : MIR.LocalId)
    (layout : LocalLayout) (valid : localId<frame.locals.size) (value : Immediate Provenance) :
    (ActualLocalCopy.written frame localId layout valid value).locals[localId]?=
      some ⟨.live (.immediate value),some layout⟩ := by
  simp [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout]

private theorem written_other (frame : CompilerFrameContext.ActualFrame) (source dest : MIR.LocalId)
    (layout : LocalLayout) (valid : dest<frame.locals.size) (value : Immediate Provenance) (different : source≠dest) :
    (ActualLocalCopy.written frame dest layout valid value).locals[source]?=frame.locals[source]? := by
  simp [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Ne.symm different]

namespace Done
variable {out} (done : Done out)
def frame := afterFrame out done.input done.base

theorem trace : SuccessfulTrace.Trace (config options (remaining+1) span) limits
    (Storage.withCurrent #[] out.frame out.machine) (Storage.withCurrent #[] done.frame (machine out)) :=
  SuccessfulTrace.append done.input.trace (.next done.step (.refl _))

theorem size : done.frame.locals.size=25:=by
  simpa only [frame,afterFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.size_set] using done.input.size

theorem body : done.frame.body=RootBody.reflected.body.body:=done.input.body
theorem identity : done.frame.bodyIdentity=RootBody.reflected.body.identity:=done.input.identity
theorem callee : done.frame.functionInstance=RootBody.reflected.functionInstance:=done.input.callee
theorem clocks : done.frame.extra.dataRace=none:=done.input.clocks
theorem location : done.frame.location=.mir ⟨6,8⟩:=rfl

theorem other (index : MIR.LocalId) (different : index≠16) : done.frame.locals[index]?=done.input.frame.locals[index]? := by
  exact written_other _ index 16 _ _ _ different

theorem slot15 : done.frame.locals[15]?=some ⟨.live (.immediate .uninit),none⟩:=
  (other done 15 (by decide)).trans done.input.dest15

theorem slot16 : done.frame.locals[16]?=some ⟨.live (.immediate
    (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete out.source.role.backing.id out.tracker.global.nextPointerTag)
        (Size.ofBytes (done.base+UInt64.ofNat checkpoint.offset))) len (layout false)).imm),some (layout false)⟩:=
  written_slot _ 16 _ _ _

theorem root_metadata : done.frame.returnPlace=out.frame.returnPlace ∧
    done.frame.returnContinuation=out.frame.returnContinuation ∧done.frame.vaList=out.frame.vaList:=
  ⟨done.input.returnPlace,done.input.continuation,done.input.vaList⟩

theorem count_slot : done.frame.locals[2]?=out.frame.locals[2]?:=
  (other done 2 (by decide)).trans done.input.second

theorem high (index : Nat) (bound : 17≤index) : done.frame.locals[index]?=out.frame.locals[index]?:=
  (other done index (by intro same;subst index;exact Nat.not_le_of_lt (by decide : 16<17) bound)).trans (done.input.facts.high index bound)

theorem immediate : CopyHelperCleanup.AllImmediate done.frame:=
  CopyHelperCleanup.all_immediate_written _ _ _ _ _ done.input.immediate

end Done

theorem prepare (nonzero : count≠0) (within : count≤len/2) : Nonempty (Done out) := by
  obtain ⟨input⟩:=CurrentCallCheckpointAcceptedControl.input out nonzero within
  obtain ⟨base,cached,pointer,nonnull,step⟩:=invoke out input
  exact ⟨⟨input,base,cached,pointer,nonnull,step⟩⟩

end
end DuplicatePrefix.CurrentCallCheckpointDefaultControl
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointDefaultControl" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved common Default statement dependency {dependency}"
