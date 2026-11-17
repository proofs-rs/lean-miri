import duplicate_prefix.CurrentCallCheckpointAsMutFacts
import duplicate_prefix.PositiveRootAddToCopy
import duplicate_prefix.CurrentCallCopyGuardReturn
namespace DuplicatePrefix.CurrentCallCheckpointCopyPrefix
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
private theorem clock_fields (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (machine : Before) :
    (CopyHelperClock.advance options remaining span machine).user.payload.ghost=machine.user.payload.ghost ∧
    (CopyHelperClock.advance options remaining span machine).user.payload.validation=machine.user.payload.validation ∧
    (CopyHelperClock.advance options remaining span machine).user.payload.payload.user.types=machine.user.payload.payload.user.types:=by
  unfold CopyHelperClock.advance PtrMetadataReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  exact ⟨rfl,rfl,rfl⟩
private theorem profile_start {before id offset length start}
    (eq : start=offset) (ready : CurrentCallBoolProtection.WindowReady before id offset length) :
    CurrentCallBoolProtection.WindowReady before id start length:=by cases eq;exact ready

private theorem bounds_setExtra (allocation : Allocation Provenance BorrowTree) (tree : BorrowTree)
    (amount : Nat) (bound : amount≤allocation.byteSize.bytes.toNat) :
    amount≤(allocation.setExtra tree).byteSize.bytes.toNat:=bound
variable {options remaining span len count place limits}
  {checkpoint : CurrentCallPostEntryCheckpoint.Checkpoint options remaining span len count place}
  (out : CurrentCallCheckpointRoot3.Output checkpoint limits)
  (done : CurrentCallCheckpointDefaultControl.Done out)
  (seed : CurrentCallCheckpointAsMutControl.Helper out done)
  (returned : CurrentCallCheckpointAsMutReturn.Returned seed)
/-- Prepare the actual raw-pointer add and copy call at root 8,4. -/
theorem prepare (budget : Nat) (dispatch : limits.callDispatch=budget+1)
    (nonzero : count≠0) (within : count≤len/2)
:
    let value := CurrentCallCheckpointAsMutReturn.value seed
    let destination := Scalar.fromPointer (config options (remaining+1) span).access.runtime.base
      (Pointer.new (Provenance.concrete out.source.role.backing.id seed.output.tag) (Size.ofBytes (done.base+UInt64.ofNat checkpoint.offset+count)))
    ∃ frame,∃ _input : CopyRootEntry.Input options limits remaining span #[] frame
        (AddOutput.machine options remaining span returned.machine) value destination count,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] returned.root returned.machine)
        (Storage.withCurrent #[] frame (AddOutput.machine options remaining span returned.machine)) ∧
      frame.body=returned.root.body ∧frame.bodyIdentity=returned.root.bodyIdentity ∧frame.functionInstance=returned.root.functionInstance ∧
      frame.extra=returned.root.extra ∧frame.returnPlace=returned.root.returnPlace ∧frame.returnContinuation=returned.root.returnContinuation ∧
      frame.vaList=returned.root.vaList ∧frame.localsIdentity=returned.root.localsIdentity ∧frame.trackCallerArg=returned.root.trackCallerArg ∧
      frame.locals.size=25 ∧frame.location=.mir ⟨8,4⟩ ∧CopyHelperCleanup.AllImmediate frame ∧
      (∀ index,index<16∨24<index→frame.locals[index]?=returned.root.locals[index]?) ∧
      frame.locals[17]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      frame.locals[19]?=some ⟨.live (.immediate (.scalar value)),some CopyCompilerFacts.sourcePointerLayout⟩ ∧
      frame.locals[21]?=some ⟨.live (.immediate (.scalar destination)),some CopyCompilerFacts.destPointerLayout⟩ ∧
      frame.locals[24]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ := by
  let value:=CurrentCallCheckpointAsMutReturn.value seed
  let held:=CurrentCallCheckpointAsMutReturn.postTracker seed
  let model:=CurrentCallCheckpointAsMutFacts.model out done seed returned
  have size:=CurrentCallCheckpointAsMutFacts.size out done seed returned
  have valid (index : Fin 25) : index.val<returned.root.locals.size:=by rw [size];exact index.isLt
  have stored (index : Fin 25) (row : LocalState Provenance LocalLayout)
      (found : returned.root.locals[index.val]?=some row) : returned.root.locals[index.val]'(valid index)=row:=
    Option.some.inj ((Array.getElem?_eq_getElem (valid index)).symm.trans found)
  have slot15:=CurrentCallCheckpointAsMutFacts.slot15 out done seed returned
  have slot2:=CurrentCallCheckpointAsMutFacts.count_slot out done seed returned
  obtain ⟨temp16,slot16⟩:=CurrentCallCheckpointAsMutFacts.slot16 out done seed returned
  obtain ⟨body,identity,callee,clocks,_,_,_⟩:=CurrentCallCheckpointAsMutFacts.metadata out done seed returned
  obtain ⟨thread,active,top⟩:=returned.active
  obtain ⟨prior,tracked,mode⟩:=model.defaultTracker
  have same : prior=held:=Option.some.inj (tracked.symm.trans returned.tracked)
  subst prior
  have positive : (0 : UInt64)<count:=by
    apply UInt64.lt_iff_toNat_lt.mpr
    have nz : count.toNat≠0:=by intro zero;exact nonzero (UInt64.toNat_inj.mp zero)
    simp only [UInt64.toNat_zero];omega
  let finalEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind:=
    {(CurrentCallCheckpointAsMutControl.entry out) with allocation:=(CurrentCallCheckpointAsMutControl.entry out).allocation.setExtra (CurrentCallCheckpointAsMutReturn.releasedTree seed)}
  have bounds : (UInt64.ofNat checkpoint.offset).toNat+len.toNat≤finalEntry.allocation.byteSize.bytes.toNat:=by
    have original:=out.source.storage.slice.bounds
    rw [out.source.allocation] at original
    have first:=bounds_setExtra (CurrentCallCheckpointDefaultControl.entry out).allocation
      (CurrentCallCheckpointDefaultControl.tree out) ((UInt64.ofNat checkpoint.offset).toNat+len.toNat) original
    exact bounds_setExtra (CurrentCallCheckpointAsMutControl.entry out).allocation
      (CurrentCallCheckpointAsMutReturn.releasedTree seed) ((UInt64.ofNat checkpoint.offset).toNat+len.toNat) first
  have trackNone:=CurrentCallCheckpointAsMutFacts.track out done seed returned
  have relevant : returned.root.extra.userRelevance>0:=by rw [CurrentCallCheckpointAsMutFacts.relevance out done seed returned];decide
  have raw : value=Scalar.fromPointer (config options (remaining+1) span).access.runtime.base
      (Pointer.new (Provenance.concrete out.source.role.backing.id seed.output.tag) (Size.ofBytes (done.base+UInt64.ofNat checkpoint.offset))):=rfl
  obtain ⟨frame,trace,resultBody,resultIdentity,resultCallee,resultExtra,returnPlace,resultContinuation,resultVarargs,resultLocalsIdentity,
    resultTrack,resultSize,resultLocation,live17,live18,live19,live21,live24,keep,resultAll⟩:=
    PositiveRootAddToCopy.executes options limits remaining span model.debugOff checkpoint.validationFuel checkpoint.validationEq #[] returned.root returned.machine
      value count temp16 size (congrArg LocalState.value (stored ⟨15,by decide⟩ _ slot15))
      (congrArg LocalState.layout (stored ⟨15,by decide⟩ _ slot15))
      (congrArg LocalState.value (stored ⟨16,by decide⟩ _ slot16))
      (congrArg LocalState.value (stored ⟨2,by decide⟩ _ slot2)) (congrArg LocalState.layout (stored ⟨2,by decide⟩ _ slot2))
      (by intro index bounded lower upper;exact Option.some.inj ((Array.getElem?_eq_getElem bounded).symm.trans
        (CurrentCallCheckpointAsMutFacts.unused out done seed returned ⟨index,by omega⟩ lower)))
      body identity callee (CurrentCallCheckpointAsMutFacts.location out done seed returned) clocks held returned.tracked mode model.ghostOff model.shallow
      (CurrentCallCheckpointAsMutFacts.immediate out done seed returned) trackNone relevant thread active top budget dispatch
      model.noBackend model.noDataRace model.unchecked model.noGc model.fixedScheduler out.source.role.backing.id seed.output.tag done.base (UInt64.ofNat checkpoint.offset) len finalEntry
      raw (CurrentCallCheckpointAsMutFacts.cached out done seed returned) returned.sourceLive positive within bounds
      (DuplicatePrefixCallModel.sourceComparator options remaining span returned.machine model) model.nullComparator
  let post:=AddOutput.machine options remaining span returned.machine
  obtain ⟨sameMemory,sameTracker,sameThreads,sameRace,sameAddresses,sameGhost,sameShallow,sameBackend,sameExtras,sameTypes⟩:=
    AddOutput.preserved options remaining span returned.machine
  have resultValid (index : Fin 25) : index.val<frame.locals.size:=by rw [resultSize];exact index.isLt
  have resultStored (index : Fin 25) (row : LocalState Provenance LocalLayout)
      (found : frame.locals[index.val]?=some row) : frame.locals[index.val]'(resultValid index)=row:=
    Option.some.inj ((Array.getElem?_eq_getElem (resultValid index)).symm.trans found)
  let input : CopyRootEntry.Input options limits remaining span #[] frame post value
      (Scalar.fromPointer (config options (remaining+1) span).access.runtime.base
        (Pointer.new (Provenance.concrete out.source.role.backing.id seed.output.tag) (Size.ofBytes (done.base+UInt64.ofNat checkpoint.offset+count)))) count:={
    debug:=model.debugOff,tracker:=held,tracked:=sameTracker.trans returned.tracked,valid:=resultValid ⟨18,by decide⟩,old:=.uninit
    live:=congrArg LocalState.value (resultStored ⟨18,by decide⟩ _ live18),uncached:=congrArg LocalState.layout (resultStored ⟨18,by decide⟩ _ live18)
    noClocks:=(congrArg (fun extra=>extra.dataRace) resultExtra).trans clocks,noRace:=sameRace.trans model.noDataRace
    body:=resultBody.trans body,identity:=resultIdentity.trans identity,callee:=resultCallee.trans callee
    trackNone:=resultTrack.trans trackNone,location:=resultLocation,fuel:=checkpoint.validationFuel,validationFuel:=checkpoint.validationEq
    ghost:=sameGhost.trans model.ghostOff,shallow:=sameShallow.trans model.shallow,thread:=thread,active:=by rw [sameThreads];exact active
    top:=top,relevant:=by rw [resultExtra];exact relevant,budget:=budget,budgetEq:=dispatch,backend:=sameBackend.trans model.noBackend
    unchecked:=by rw [AddOutput.control];exact model.unchecked,noGc:=by rw [AddOutput.control];exact model.noGc
    fixed:=by rw [sameThreads];exact model.fixedScheduler
    source:=DuplicatePrefixCallModel.sourceComparator options remaining span returned.machine model,cmp:=model.nullComparator
    valid19:=resultValid ⟨19,by decide⟩,valid21:=resultValid ⟨21,by decide⟩,valid24:=resultValid ⟨24,by decide⟩
    live19:=congrArg LocalState.value (resultStored ⟨19,by decide⟩ _ live19),cache19:=congrArg LocalState.layout (resultStored ⟨19,by decide⟩ _ live19)
    live21:=congrArg LocalState.value (resultStored ⟨21,by decide⟩ _ live21),cache21:=congrArg LocalState.layout (resultStored ⟨21,by decide⟩ _ live21)
    live24:=congrArg LocalState.value (resultStored ⟨24,by decide⟩ _ live24),cache24:=congrArg LocalState.layout (resultStored ⟨24,by decide⟩ _ live24)}
  exact ⟨frame,input,trace,resultBody,resultIdentity,resultCallee,resultExtra,returnPlace,resultContinuation,resultVarargs,
    resultLocalsIdentity,resultTrack,resultSize,resultLocation,resultAll,keep,live17,live19,live21,live24⟩


def allocation := (CurrentCallCheckpointAsMutControl.entry out).allocation.setExtra (CurrentCallCheckpointAsMutReturn.releasedTree seed)

def readAccess := (allocation out done seed).extra.performBorrowAccessRange (.concrete seed.output.tag)
  (Size.ofBytes (UInt64.ofNat checkpoint.offset)) (Size.ofBytes count) .Read
  (CurrentCallCheckpointAsMutReturn.postTracker seed).global.protectedTags .VisitChildrenOfAccessed

def writeAccess := (readAccess out done seed).tree.performBorrowAccessRange (.concrete seed.output.tag)
  (Size.ofBytes (UInt64.ofNat checkpoint.offset+count)) (Size.ofBytes count) .Write
  (CurrentCallCheckpointAsMutReturn.postTracker seed).global.protectedTags .VisitChildrenOfAccessed

private theorem maximum (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    (config options remaining span).projection.maxSizeOfVal=Size.ofBytes 9223372036854775807:=by
  have fields:=CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨_,_,_,_,projectionEq,_⟩:=fields.placeConstruction
  have same : (config options remaining span).projection.maxSizeOfVal=(config options remaining span).projection.dynamic.maxSizeOfVal:=by rw [projectionEq];rfl
  obtain ⟨_,bound,boundEq,dynamicEq⟩:=fields.projectionDynamic
  rw [same,dynamicEq]
  change bound=Size.ofBytes 9223372036854775807
  exact Except.ok.inj (boundEq.symm.trans (show CompilerExecutionBounds.maximum PreparedReflection.actual.compiler.runtime.target=
    .ok (Size.ofBytes 9223372036854775807) from rfl))

/-- Pure copy execution consumes the two certificates from the common
full-bank subrange producer; physical storage/profile are derived here. -/
theorem copied (budget : Nat) (dispatch : limits.callDispatch=budget+1)
    (statementFuel : Nat) (statementEq : limits.validation=statementFuel+1)
    (nonzero : count≠0) (within : count≤len/2)
    (readDone : (readAccess out done seed).status=.Completed)
    (writeDone : (writeAccess out done seed).status=.Completed) :
    ∃ frame machine copied,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] returned.root returned.machine) (Storage.withCurrent #[] frame machine) ∧
      frame.location=.mir ⟨9,0⟩ ∧frame.body=returned.root.body ∧frame.bodyIdentity=returned.root.bodyIdentity ∧
      frame.functionInstance=returned.root.functionInstance ∧frame.returnPlace=returned.root.returnPlace ∧
      frame.returnContinuation=returned.root.returnContinuation ∧frame.vaList=returned.root.vaList ∧frame.extra=returned.root.extra ∧
      CopyHelperCleanup.AllImmediate frame ∧frame.locals.size=25 ∧
      frame.locals[17]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      frame.locals[18]?=some ⟨.live (.immediate .uninit),some CopyHelperUnit.layout⟩ ∧
      frame.locals[19]?=some ⟨.live (.immediate (.scalar (CurrentCallCheckpointAsMutReturn.value seed))),some CopyCompilerFacts.sourcePointerLayout⟩ ∧
      frame.locals[21]?=some ⟨.live (.immediate (.scalar (Scalar.fromPointer (config options (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete out.source.role.backing.id seed.output.tag) (Size.ofBytes (done.base+UInt64.ofNat checkpoint.offset+count)))))),some CopyCompilerFacts.destPointerLayout⟩ ∧
      frame.locals[24]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ ∧
      (∀ index,index<16→frame.locals[index]?=returned.root.locals[index]?) ∧
      machine.memory.live.find? (fun row=>row.1==out.source.role.backing.id)=some (out.source.role.backing.id,⟨(CurrentCallCheckpointAsMutControl.entry out).kind,copied⟩) ∧
      copied.byteSize=(allocation out done seed).byteSize ∧copied.len=(allocation out done seed).len ∧
      AllocationCopy.snapshot copied=(AllocationCopy.snapshot (allocation out done seed)).extract 0 (UInt64.ofNat checkpoint.offset+count).toNat ++
        (AllocationCopy.snapshot (allocation out done seed)).extract (UInt64.ofNat checkpoint.offset).toNat (UInt64.ofNat checkpoint.offset+count).toNat ++
        (AllocationCopy.snapshot (allocation out done seed)).extract (UInt64.ofNat checkpoint.offset+count+count).toNat (allocation out done seed).len ∧
      copied.extra=(writeAccess out done seed).tree ∧S02SameDestinationAcceptedCopyPhysical.Physical copied ∧
      machine.borrowTracker=some (CurrentCallCheckpointAsMutReturn.postTracker seed) ∧
      DuplicatePrefixCallModel.Model options remaining span machine ∧
      DuplicatePrefixTypeCacheOrigins.Origins machine.user.payload.payload.user.types ∧
      machine.user.addresses=returned.machine.user.addresses ∧
      machine.user.payload.payload.user.runtime.extras=returned.machine.user.payload.payload.user.runtime.extras ∧
      (∃ thread,machine.threads.activeThread?=some thread) ∧
      machine.memory=(CanonicalCopy.replaceAllocation (Storage.withCurrent #[] returned.root (AddOutput.machine options remaining span returned.machine))
        out.source.role.backing.id (CurrentCallCheckpointAsMutControl.entry out).kind copied).machine.memory := by
  obtain ⟨frame,input,trace,body,identity,callee,extra,destination,continuation,varargs,localsIdentity,track,size,located,all,keep,slot17,slot19,slot21,slot24⟩:=
    prepare out done seed returned budget dispatch nonzero within
  let post:=AddOutput.machine options remaining span returned.machine
  have preserved:=AddOutput.preserved options remaining span returned.machine
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind:=
    {CurrentCallCheckpointAsMutControl.entry out with allocation:=allocation out done seed}
  have live : post.memory.live.find? (fun row=>row.1==out.source.role.backing.id)=some (out.source.role.backing.id,entry):=by
    rw [preserved.1]
    exact returned.sourceLive
  have data : CurrentCallResourceEntrySourceStorage.Data entry.allocation (UInt64.ofNat checkpoint.offset) len:=by
    have initial:=out.source.storage
    rw [out.source.allocation] at initial
    exact (initial.set_extra (CurrentCallCheckpointDefaultControl.tree out)).set_extra (CurrentCallCheckpointAsMutReturn.releasedTree seed)
  have profile:=out.source.profile.transport (CurrentCallCheckpointAsMutFacts.extras out done seed returned)
  have profileNow:=profile.transport preserved.2.2.2.2.2.2.2.2.1
  have startEq : (UInt64.ofNat checkpoint.offset).toNat=checkpoint.offset:=CurrentCallCheckpointShared.start_eq checkpoint
  have profileAt:=profile_start startEq profileNow
  have cached : post.user.addresses.baseAddr.find? (fun row=>row.allocId==out.source.role.backing.id)=some ⟨out.source.role.backing.id,done.base⟩:=by
    rw [preserved.2.2.2.2.1]
    exact CurrentCallCheckpointAsMutFacts.cached out done seed returned
  have positive : (0:UInt64)<count:=by
    apply UInt64.lt_iff_toNat_lt.mpr
    have nz : count.toNat≠0:=by intro zero;exact nonzero (UInt64.toNat_inj.mp zero)
    simp only [UInt64.toNat_zero];omega
  have trackerEq : input.tracker=CurrentCallCheckpointAsMutReturn.postTracker seed:=
    Option.some.inj (input.tracked.symm.trans (preserved.2.1.trans returned.tracked))
  have mode : input.tracker.retagMode=.Default:=by rw [trackerEq];exact CurrentCallCheckpointDefaultControl.mode out
  have numeric:=PositiveRootCopyBounds.guarded len count (UInt64.ofNat checkpoint.offset) entry.allocation.byteSize.bytes within data.slice.bounds
  have fits : (UInt64.ofNat checkpoint.offset).toNat+len.toNat<2^64:=Nat.lt_of_le_of_lt data.slice.bounds entry.allocation.byteSize.bytes.toNat_lt
  have middle : (UInt64.ofNat checkpoint.offset+count).toNat=(UInt64.ofNat checkpoint.offset).toNat+count.toNat:=by
    simp only [UInt64.toNat_add,Nat.mod_eq_of_lt (by omega : (UInt64.ofNat checkpoint.offset).toNat+count.toNat<2^64)]
  have readReady:=profileAt.subrange (UInt64.ofNat checkpoint.offset).toNat count.toNat (Nat.le_refl _) (by omega)
  have writeReady:=profileAt.subrange (UInt64.ofNat checkpoint.offset+count).toNat count.toNat (by omega) (by omega)
  have initialized:=DuplicatePrefixSliceStorage.accepted_initialized _ _ _ _ count data.slice within
  have first : (entry.allocation.extra.performBorrowAccessRange (.concrete seed.output.tag) (Size.ofBytes (UInt64.ofNat checkpoint.offset)) (Size.ofBytes count)
      .Read input.tracker.global.protectedTags .VisitChildrenOfAccessed).status=.Completed:=by
    rw [trackerEq]
    exact readDone
  have second : ((entry.allocation.extra.performBorrowAccessRange (.concrete seed.output.tag) (Size.ofBytes (UInt64.ofNat checkpoint.offset)) (Size.ofBytes count)
      .Read input.tracker.global.protectedTags .VisitChildrenOfAccessed).tree.performBorrowAccessRange (.concrete seed.output.tag)
      (Size.ofBytes (UInt64.ofNat checkpoint.offset+count)) (Size.ofBytes count) .Write input.tracker.global.protectedTags .VisitChildrenOfAccessed).status=.Completed:=by
    rw [trackerEq]
    exact writeDone
  have bounded : count≤(config options (remaining+1) span).projection.maxSizeOfVal.bytes:=by
    rw [maximum]
    apply UInt64.le_iff_toNat_le.mpr
    have accepted:=UInt64.le_iff_toNat_le.mp within
    have signed:=checkpoint.source.signedFits
    rw [UInt64.toNat_div] at accepted
    change count.toNat≤9223372036854775807
    omega
  obtain ⟨guardMachine,copied,machine,copyTrace,guardPreserved,copiedLive,bytes,length,tree,snapshot,physical,memory,tracked,user,race,fixed,actor⟩:=
    CurrentCallCopyGuardReturn.run options limits remaining span #[] frame post _ _ count input statementFuel statementEq mode
      out.source.role.backing.id seed.output.tag done.base (UInt64.ofNat checkpoint.offset) len entry.kind entry.allocation positive data.slice.bounds numeric.2.1
      data.storage data.slice.maskValid data.slice.maskLength initialized data.provenance data.storageFits data.mutable
      readReady writeReady live cached first second bounded rfl (by
        exact congrArg (Scalar.fromPointer (config options (remaining+1) span).access.runtime.base)
          (congrArg (Pointer.new (Provenance.concrete out.source.role.backing.id seed.output.tag)) (congrArg Size.ofBytes (UInt64.add_assoc done.base (UInt64.ofNat checkpoint.offset) count))))
  let oldModel:=CurrentCallCheckpointAsMutFacts.model out done seed returned
  let first:=CopyHelperClock.advance options remaining span guardMachine
  let second:=CopyHelperClock.advance options remaining span first
  have ghostEq:=(clock_fields options remaining span second).1.trans ((clock_fields options remaining span first).1.trans (clock_fields options remaining span guardMachine).1)
  have shallowEq:=(clock_fields options remaining span second).2.1.trans ((clock_fields options remaining span first).2.1.trans (clock_fields options remaining span guardMachine).2.1)
  have typesEq:=(clock_fields options remaining span second).2.2.trans ((clock_fields options remaining span first).2.2.trans (clock_fields options remaining span guardMachine).2.2)
  have finalTypes : machine.user.payload.payload.user.types=returned.machine.user.payload.payload.user.types:=
    (congrArg (fun user=>user.payload.payload.user.types) user).trans (typesEq.trans (guardPreserved.types.trans preserved.2.2.2.2.2.2.2.2.2))
  have finalModel : DuplicatePrefixCallModel.Model options remaining span machine:={oldModel with
    ghostOff:=(congrArg (fun user=>user.payload.ghost) user).trans (ghostEq.trans (guardPreserved.ghost.trans (preserved.2.2.2.2.2.1.trans oldModel.ghostOff)))
    shallow:=(congrArg (fun user=>user.payload.validation) user).trans (shallowEq.trans (guardPreserved.validation.trans (preserved.2.2.2.2.2.2.1.trans oldModel.shallow)))
    defaultTracker:=⟨_,tracked.trans (congrArg some trackerEq),by exact CurrentCallCheckpointDefaultControl.mode out⟩
    noDataRace:=race.trans (preserved.2.2.2.1.trans oldModel.noDataRace)
    noBackend:=by rw [user];simp only [CopyHelperClock.backend];exact guardPreserved.backend.trans (preserved.2.2.2.2.2.2.2.1.trans oldModel.noBackend)
    metadata:=by rw [finalTypes];exact oldModel.metadata
    fixedScheduler:=fixed.trans ((congrArg (fun threads=>threads.fixedScheduling) preserved.2.2.1).trans oldModel.fixedScheduler)
    unchecked:=by rw [user];simp only [CopyHelperClock.control,TerminatorClock.advance];exact guardPreserved.unchecked.trans (by rw [AddOutput.control];exact oldModel.unchecked)
    noGc:=by rw [user];simp only [CopyHelperClock.control,TerminatorClock.advance];exact guardPreserved.noGc.trans (by rw [AddOutput.control];exact oldModel.noGc)}
  have finalAddresses : machine.user.addresses=returned.machine.user.addresses:=by
    rw [user];simp only [CopyHelperClock.addresses];exact guardPreserved.addresses.trans preserved.2.2.2.2.1
  have finalExtras : machine.user.payload.payload.user.runtime.extras=returned.machine.user.payload.payload.user.runtime.extras:=by
    rw [user];simp only [CopyHelperClock.runtime];exact guardPreserved.extras.trans preserved.2.2.2.2.2.2.2.2.1
  have projections:=CurrentCallCopyGuardReturn.frame_projections options limits remaining span #[] frame post _ _ count input
  refine ⟨_,machine,copied,SuccessfulTrace.append trace copyTrace,projections.2.2.2.2.2.2.2.2.2.2.1,
    projections.1.trans body,projections.2.1.trans identity,projections.2.2.1.trans callee,
    projections.2.2.2.2.1.trans destination,projections.2.2.2.2.2.1.trans continuation,projections.2.2.2.2.2.2.1.trans varargs,
    projections.2.2.2.1.trans extra,
    CurrentCallCopyGuardReturn.all_immediate options limits remaining span #[] frame post _ _ count input all,
    projections.2.2.2.2.2.2.2.2.2.1.trans size,
    (projections.2.2.2.2.2.2.2.2.2.2.2.2 17 (by decide)).trans slot17,
    projections.2.2.2.2.2.2.2.2.2.2.2.1,
    (projections.2.2.2.2.2.2.2.2.2.2.2.2 19 (by decide)).trans slot19,
    (projections.2.2.2.2.2.2.2.2.2.2.2.2 21 (by decide)).trans slot21,
    (projections.2.2.2.2.2.2.2.2.2.2.2.2 24 (by decide)).trans slot24,
    ?_,copiedLive,bytes,length,snapshot,?_,physical,?_,finalModel,?_,finalAddresses,finalExtras,actor,memory⟩
  · intro index bound
    exact (projections.2.2.2.2.2.2.2.2.2.2.2.2 index (by omega)).trans (keep index (.inl bound))
  · simpa only [entry,readAccess,writeAccess,trackerEq] using tree
  · exact tracked.trans (congrArg some trackerEq)
  · rw [finalTypes]
    exact CurrentCallCheckpointAsMutFacts.origins out done seed returned

structure Copied where
  frame : CompilerFrameContext.ActualFrame
  machine : Before
  allocation : Allocation Provenance BorrowTree
  trace : SuccessfulTrace.Trace (config options (remaining+1) span) limits
    (Storage.withCurrent #[] returned.root returned.machine) (Storage.withCurrent #[] frame machine)
  location : frame.location=.mir ⟨9,0⟩
  body : frame.body=returned.root.body
  identity : frame.bodyIdentity=returned.root.bodyIdentity
  callee : frame.functionInstance=returned.root.functionInstance
  destination : frame.returnPlace=returned.root.returnPlace
  continuation : frame.returnContinuation=returned.root.returnContinuation
  varargs : frame.vaList=returned.root.vaList
  extra : frame.extra=returned.root.extra
  immediate : CopyHelperCleanup.AllImmediate frame
  size : frame.locals.size=25
  slot17 : frame.locals[17]?=some ⟨.live (.immediate .uninit),none⟩
  slot18 : frame.locals[18]?=some ⟨.live (.immediate .uninit),some CopyHelperUnit.layout⟩
  slot19 : frame.locals[19]?=some ⟨.live (.immediate (.scalar (CurrentCallCheckpointAsMutReturn.value seed))),some CopyCompilerFacts.sourcePointerLayout⟩
  slot21 : frame.locals[21]?=some ⟨.live (.immediate (.scalar (Scalar.fromPointer (config options (remaining+1) span).access.runtime.base
    (Pointer.new (Provenance.concrete out.source.role.backing.id seed.output.tag) (Size.ofBytes (done.base+UInt64.ofNat checkpoint.offset+count)))))),some CopyCompilerFacts.destPointerLayout⟩
  slot24 : frame.locals[24]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
  keep : ∀ index,index<16→frame.locals[index]?=returned.root.locals[index]?
  live : machine.memory.live.find? (fun row=>row.1==out.source.role.backing.id)=some (out.source.role.backing.id,⟨(CurrentCallCheckpointAsMutControl.entry out).kind,allocation⟩)
  byteSize : allocation.byteSize=(CurrentCallCheckpointCopyPrefix.allocation out done seed).byteSize
  length : allocation.len=(CurrentCallCheckpointCopyPrefix.allocation out done seed).len
  snapshot : AllocationCopy.snapshot allocation=(AllocationCopy.snapshot (CurrentCallCheckpointCopyPrefix.allocation out done seed)).extract 0 (UInt64.ofNat checkpoint.offset+count).toNat ++
    (AllocationCopy.snapshot (CurrentCallCheckpointCopyPrefix.allocation out done seed)).extract (UInt64.ofNat checkpoint.offset).toNat (UInt64.ofNat checkpoint.offset+count).toNat ++
    (AllocationCopy.snapshot (CurrentCallCheckpointCopyPrefix.allocation out done seed)).extract (UInt64.ofNat checkpoint.offset+count+count).toNat (CurrentCallCheckpointCopyPrefix.allocation out done seed).len
  tree : allocation.extra=(writeAccess out done seed).tree
  physical : S02SameDestinationAcceptedCopyPhysical.Physical allocation
  tracked : machine.borrowTracker=some (CurrentCallCheckpointAsMutReturn.postTracker seed)
  model : DuplicatePrefixCallModel.Model options remaining span machine
  origins : DuplicatePrefixTypeCacheOrigins.Origins machine.user.payload.payload.user.types
  addresses : machine.user.addresses=returned.machine.user.addresses
  extras : machine.user.payload.payload.user.runtime.extras=returned.machine.user.payload.payload.user.runtime.extras
  active : ∃ thread,machine.threads.activeThread?=some thread
  memory : machine.memory=(CanonicalCopy.replaceAllocation (Storage.withCurrent #[] returned.root (AddOutput.machine options remaining span returned.machine)) out.source.role.backing.id (CurrentCallCheckpointAsMutControl.entry out).kind allocation).machine.memory


/-- Package the actual root-9 output; the access producer discharges these
internal certificates before the common safety theorem invokes this seam. -/
theorem of_steps (budget : Nat) (dispatch : limits.callDispatch=budget+1)
    (statementFuel : Nat) (statementEq : limits.validation=statementFuel+1)
    (nonzero : count≠0) (within : count≤len/2)
    (readDone : (readAccess out done seed).status=.Completed)
    (writeDone : (writeAccess out done seed).status=.Completed) : Nonempty (Copied out done seed returned) := by
  obtain ⟨frame,machine,allocation,trace,location,body,identity,callee,destination,continuation,varargs,extra,immediate,size,
    slot17,slot18,slot19,slot21,slot24,keep,live,bytes,length,snapshot,tree,physical,tracked,model,origins,addresses,extras,active,memory⟩:=
      copied out done seed returned budget dispatch statementFuel statementEq nonzero within readDone writeDone
  exact ⟨⟨frame,machine,allocation,trace,location,body,identity,callee,destination,continuation,varargs,extra,immediate,size,
    slot17,slot18,slot19,slot21,slot24,keep,live,bytes,length,snapshot,tree,physical,tracked,model,origins,addresses,extras,active,memory⟩⟩

end
end DuplicatePrefix.CurrentCallCheckpointCopyPrefix
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointCopyPrefix" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved common copy prefix dependency {dependency}"
