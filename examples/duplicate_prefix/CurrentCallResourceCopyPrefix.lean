import duplicate_prefix.CurrentCallResourceAsMutFacts
import duplicate_prefix.CurrentCallResourceCopyGuard
import duplicate_prefix.CurrentCallResourceSameHeap
import duplicate_prefix.PositiveRootAddToCopy
namespace DuplicatePrefix.CurrentCallResourceCopyPrefix
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallResourceEntryBody
open CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section
private theorem clock_fields (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (machine : Before) :
    (CopyHelperClock.advance options remaining span machine).user.payload.ghost=machine.user.payload.ghost ∧
    (CopyHelperClock.advance options remaining span machine).user.payload.validation=machine.user.payload.validation ∧
    (CopyHelperClock.advance options remaining span machine).user.payload.payload.user.types=machine.user.payload.payload.user.types:=by
  unfold CopyHelperClock.advance PtrMetadataReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  exact ⟨rfl,rfl,rfl⟩
private def tracker_window {before old next data owner id offset length mode}
    (eq : old=next) (W : UniformWindow before old data owner id offset length mode) :
    UniformWindow before next data owner id offset length mode:=eq ▸ W
private theorem tracker_allocation {before old next data owner id offset length mode}
    (eq : old=next) (W : UniformWindow before old data owner id offset length mode) :
    (tracker_window eq W).allocation=W.allocation:=by cases eq;rfl
private theorem tracker_pointer {before old next data owner id offset length mode}
    (eq : old=next) (W : UniformWindow before old data owner id offset length mode) :
    (tracker_window eq W).pointer=W.pointer:=by cases eq;rfl
variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    {out : Output limits C count} {ready : CurrentCallResourceBodyReadiness.Ready C} {nextData nextOwner}
    {Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut}
    {stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)}
    {result : CurrentCallResourceLenReturn.Result out ready Q stage}
    (done : CurrentCallResourceAsMutInvoke.DefaultResult result)
    (fresh : done.nextTracker.global.nextPointerTag.value<18446744073709551615)
    (valid15 : (15 : MIR.LocalId)<done.frame.locals.size)
    (seed : CurrentCallResourceAsMutCall.Seed options limits remaining span done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15)
    (returned : CurrentCallResourceAsMutReturn.Returned done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed)

/-- Prepare the actual raw-pointer add and copy call at root 8,4. -/
theorem prepare (budget : Nat) (dispatch : limits.callDispatch=budget+1)
    (nonzero : count≠0) (within : count≤len/2)
    (trackNone : returned.root.trackCallerArg=none)
    (relevant : returned.root.extra.userRelevance>0) :
    let value := CurrentCallResourceAsMutReturn.value done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed
    let destination := Scalar.fromPointer (config options (remaining+1) span).access.runtime.base
      (Pointer.new (Provenance.concrete id seed.output.tag) (Size.ofBytes (done.base+UInt64.ofNat offset+count)))
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
  let value:=CurrentCallResourceAsMutReturn.value done.current done.entry done.frame done.base
    (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed
  let held:=CurrentCallResourceAsMutReturn.postTracker done.current done.entry done.frame done.base
    (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed
  let model:=CurrentCallResourceAsMutFacts.model done fresh valid15 seed returned
  have size:=CurrentCallResourceAsMutFacts.size done fresh valid15 seed returned
  have valid (index : Fin 25) : index.val<returned.root.locals.size:=by rw [size];exact index.isLt
  have stored (index : Fin 25) (row : LocalState Provenance LocalLayout)
      (found : returned.root.locals[index.val]?=some row) : returned.root.locals[index.val]'(valid index)=row:=
    Option.some.inj ((Array.getElem?_eq_getElem (valid index)).symm.trans found)
  have slot15:=CurrentCallResourceAsMutFacts.slot15 done fresh valid15 seed returned
  have slot2:=CurrentCallResourceAsMutFacts.count_slot done fresh valid15 seed returned
  obtain ⟨temp16,slot16⟩:=CurrentCallResourceAsMutFacts.slot16 done fresh valid15 seed returned
  obtain ⟨body,identity,callee,clocks,_,_,_⟩:=CurrentCallResourceAsMutFacts.metadata done fresh valid15 seed returned
  obtain ⟨thread,active,top⟩:=returned.active
  obtain ⟨prior,tracked,mode⟩:=model.defaultTracker
  have same : prior=held:=Option.some.inj (tracked.symm.trans returned.tracked)
  subst prior
  have positive : (0 : UInt64)<count:=by
    apply UInt64.lt_iff_toNat_lt.mpr
    have nz : count.toNat≠0:=by intro zero;exact nonzero (UInt64.toNat_inj.mp zero)
    simp only [UInt64.toNat_zero];omega
  have allocation := seed.allocationEq
  let finalEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind:=
    {done.entry with allocation:=done.entry.allocation.setExtra (CurrentCallResourceAsMutReturn.releasedTree done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed)}
  have bounds : (UInt64.ofNat offset).toNat+len.toNat≤finalEntry.allocation.byteSize.bytes.toNat:=by
    change (UInt64.ofNat offset).toNat+len.toNat≤done.entry.allocation.byteSize.bytes.toNat
    have capacity : seed.output.child.tree.locations.size=done.entry.allocation.byteSize:=
      seed.witness.capacity.trans (done.current.issued.capability.treeExtent.trans (congrArg Allocation.byteSize seed.allocationEq))
    rw [←capacity]
    exact seed.bounds
  have raw : value=Scalar.fromPointer (config options (remaining+1) span).access.runtime.base
      (Pointer.new (Provenance.concrete id seed.output.tag) (Size.ofBytes (done.base+UInt64.ofNat offset))):=rfl
  obtain ⟨frame,trace,resultBody,resultIdentity,resultCallee,resultExtra,returnPlace,resultContinuation,resultVarargs,resultLocalsIdentity,
    resultTrack,resultSize,resultLocation,live17,live18,live19,live21,live24,keep,resultAll⟩:=
    PositiveRootAddToCopy.executes options limits remaining span model.debugOff C.validationFuel C.validationEq #[] returned.root returned.machine
      value count temp16 size (congrArg LocalState.value (stored ⟨15,by decide⟩ _ slot15))
      (congrArg LocalState.layout (stored ⟨15,by decide⟩ _ slot15))
      (congrArg LocalState.value (stored ⟨16,by decide⟩ _ slot16))
      (congrArg LocalState.value (stored ⟨2,by decide⟩ _ slot2)) (congrArg LocalState.layout (stored ⟨2,by decide⟩ _ slot2))
      (by intro index bounded lower upper;exact Option.some.inj ((Array.getElem?_eq_getElem bounded).symm.trans
        (CurrentCallResourceAsMutFacts.unused done fresh valid15 seed returned ⟨index,by omega⟩ lower)))
      body identity callee (CurrentCallResourceAsMutFacts.location done fresh valid15 seed returned) clocks held returned.tracked mode model.ghostOff model.shallow
      (CurrentCallResourceAsMutFacts.immediate done fresh valid15 seed returned) trackNone relevant thread active top budget dispatch
      model.noBackend model.noDataRace model.unchecked model.noGc model.fixedScheduler id seed.output.tag done.base (UInt64.ofNat offset) len finalEntry
      raw (CurrentCallResourceAsMutFacts.cached done fresh valid15 seed returned) returned.sourceLive positive within bounds
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
        (Pointer.new (Provenance.concrete id seed.output.tag) (Size.ofBytes (done.base+UInt64.ofNat offset+count)))) count:={
    debug:=model.debugOff,tracker:=held,tracked:=sameTracker.trans returned.tracked,valid:=resultValid ⟨18,by decide⟩,old:=.uninit
    live:=congrArg LocalState.value (resultStored ⟨18,by decide⟩ _ live18),uncached:=congrArg LocalState.layout (resultStored ⟨18,by decide⟩ _ live18)
    noClocks:=(congrArg (fun extra=>extra.dataRace) resultExtra).trans clocks,noRace:=sameRace.trans model.noDataRace
    body:=resultBody.trans body,identity:=resultIdentity.trans identity,callee:=resultCallee.trans callee
    trackNone:=resultTrack.trans trackNone,location:=resultLocation,fuel:=C.validationFuel,validationFuel:=C.validationEq
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
/-- Actual accepted byte copy and helper return, using initialized physical
storage and the selected profile capability at the current root. -/
theorem copied (budget : Nat) (dispatch : limits.callDispatch=budget+1)
    (statementFuel : Nat) (statementEq : limits.validation=statementFuel+1)
    (nonzero : count≠0) (within : count≤len/2)
    (trackNone : returned.root.trackCallerArg=none) (relevant : returned.root.extra.userRelevance>0)
    (storage : CurrentCallResourceEntrySourceStorage.Data done.current.allocation (UInt64.ofNat offset) len)
    (profile : CurrentCallBoolProtection.WindowReady returned.machine id (UInt64.ofNat offset).toNat len.toNat)
    (bounded : count≤(config options (remaining+1) span).projection.maxSizeOfVal.bytes) :
    ∃ frame machine copied,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] returned.root returned.machine) (Storage.withCurrent #[] frame machine) ∧
      frame.location=.mir ⟨9,0⟩ ∧frame.body=returned.root.body ∧frame.bodyIdentity=returned.root.bodyIdentity ∧
      frame.functionInstance=returned.root.functionInstance ∧frame.returnPlace=returned.root.returnPlace ∧
      frame.returnContinuation=returned.root.returnContinuation ∧frame.vaList=returned.root.vaList ∧frame.extra=returned.root.extra ∧
      CopyHelperCleanup.AllImmediate frame ∧frame.locals.size=25 ∧
      frame.locals[17]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      frame.locals[18]?=some ⟨.live (.immediate .uninit),some CopyHelperUnit.layout⟩ ∧
      frame.locals[19]?=some ⟨.live (.immediate (.scalar (CurrentCallResourceAsMutReturn.value done.current done.entry done.frame done.base
        (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed))),some CopyCompilerFacts.sourcePointerLayout⟩ ∧
      frame.locals[21]?=some ⟨.live (.immediate (.scalar (Scalar.fromPointer (config options (remaining+1) span).access.runtime.base
        (Pointer.new (Provenance.concrete id seed.output.tag) (Size.ofBytes (done.base+UInt64.ofNat offset+count)))))),some CopyCompilerFacts.destPointerLayout⟩ ∧
      frame.locals[24]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ ∧
      (∀ index,index<16→frame.locals[index]?=returned.root.locals[index]?) ∧
      machine.memory.live.find? (fun row=>row.1==id)=some (id,⟨done.entry.kind,copied⟩) ∧
      copied.byteSize=done.current.allocation.byteSize ∧copied.len=done.current.allocation.len ∧
      AllocationCopy.snapshot copied=(AllocationCopy.snapshot done.current.allocation).extract 0 (UInt64.ofNat offset+count).toNat ++
        (AllocationCopy.snapshot done.current.allocation).extract (UInt64.ofNat offset).toNat (UInt64.ofNat offset+count).toNat ++
        (AllocationCopy.snapshot done.current.allocation).extract (UInt64.ofNat offset+count+count).toNat done.current.allocation.len ∧
      copied.extra=(((CurrentCallResourceAsMutReturn.releasedTree done.current done.entry done.frame done.base
        (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed).performBorrowAccessRange
        (.concrete seed.output.tag) (Size.ofBytes (UInt64.ofNat offset)) (Size.ofBytes count) .Read
        (CurrentCallResourceAsMutReturn.postTracker done.current done.entry done.frame done.base
          (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed).global.protectedTags .VisitChildrenOfAccessed).tree.performBorrowAccessRange
        (.concrete seed.output.tag) (Size.ofBytes (UInt64.ofNat offset+count)) (Size.ofBytes count) .Write
        (CurrentCallResourceAsMutReturn.postTracker done.current done.entry done.frame done.base
          (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed).global.protectedTags .VisitChildrenOfAccessed).tree ∧
      S02SameDestinationAcceptedCopyPhysical.Physical copied ∧
      machine.borrowTracker=some (CurrentCallResourceAsMutReturn.postTracker done.current done.entry done.frame done.base
        (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed) ∧
      DuplicatePrefixCallModel.Model options remaining span machine ∧
      DuplicatePrefixTypeCacheOrigins.Origins machine.user.payload.payload.user.types ∧
      machine.user.addresses=returned.machine.user.addresses ∧
      machine.user.payload.payload.user.runtime.extras=returned.machine.user.payload.payload.user.runtime.extras ∧
      (∃ thread,machine.threads.activeThread?=some thread) ∧
      machine.memory=(CanonicalCopy.replaceAllocation (Storage.withCurrent #[] returned.root (AddOutput.machine options remaining span returned.machine)) id done.entry.kind copied).machine.memory := by
  obtain ⟨frame,input,trace,body,identity,callee,extra,destination,continuation,varargs,localsIdentity,track,size,located,all,keep,slot17,slot19,slot21,slot24⟩:=
    prepare done fresh valid15 seed returned budget dispatch nonzero within trackNone relevant
  let post:=AddOutput.machine options remaining span returned.machine
  have preserved:=AddOutput.preserved options remaining span returned.machine
  obtain ⟨childData,childOwner,child,pointerEq,allocationEq,completionEq⟩:=
    CurrentCallResourceAsMutReturn.current_post done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed returned
  let current:=CurrentCallResourceSameHeap.window preserved.1 child
  have currentAllocation : current.allocation=done.current.allocation.setExtra
      (CurrentCallResourceAsMutReturn.releasedTree done.current done.entry done.frame done.base
        (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed):=allocationEq
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind:=
    {done.entry with allocation:=done.entry.allocation.setExtra (CurrentCallResourceAsMutReturn.releasedTree done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed)}
  have entryEq : entry.allocation=current.allocation:=by rw [currentAllocation,seed.allocationEq]
  have live : post.memory.live.find? (fun row=>row.1==id)=some (id,entry):=by rw [preserved.1];exact returned.sourceLive
  have currentRuntime : DuplicatePrefixBorrowContract.RuntimeFacts current.allocation.extra
      (CurrentCallResourceAsMutReturn.postTracker done.current done.entry done.frame done.base
        (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed).global:=by
    rw [currentAllocation]
    exact CurrentCallResourceAsMutReturn.runtime_end_call done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed
  have releaseShape:=(CurrentCallResourceAsMutReturn.release done.current done.entry done.frame done.base
    (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed).2.1
  have currentRoots : current.allocation.extra.roots=seed.output.child.tree.roots:=by
    rw [currentAllocation];change (CurrentCallResourceAsMutReturn.releasedTree _ _ _ _ _ _ _ _).roots=_
    rw [CurrentCallResourceAsMutReturn.releasedTree,releaseShape]
  have currentNodes : current.allocation.extra.nodes=seed.output.child.tree.nodes:=by
    rw [currentAllocation];change (CurrentCallResourceAsMutReturn.releasedTree _ _ _ _ _ _ _ _).nodes=_
    rw [CurrentCallResourceAsMutReturn.releasedTree,releaseShape]
  have distinct : current.allocation.extra.roots.toList.Nodup:=by rw [currentRoots];exact seed.distinct
  have short : current.allocation.extra.nodes.size<65536:=by rw [currentNodes];exact seed.short
  have concrete : current.pointer.value.provenance=.concrete id seed.output.tag:=by
    change child.pointer.value.provenance=_
    rw [pointerEq];rfl
  have data : CurrentCallResourceEntrySourceStorage.Data entry.allocation (UInt64.ofNat offset) len:=by
    rw [entryEq,currentAllocation]
    exact storage.set_extra _
  have profileNow:=profile.transport preserved.2.2.2.2.2.2.2.2.1
  have cached : post.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,done.base⟩:=by
    rw [preserved.2.2.2.2.1]
    exact CurrentCallResourceAsMutFacts.cached done fresh valid15 seed returned
  have positive : (0 : UInt64)<count:=by
    apply UInt64.lt_iff_toNat_lt.mpr
    have nz : count.toNat≠0:=by intro zero;exact nonzero (UInt64.toNat_inj.mp zero)
    simp only [UInt64.toNat_zero];omega
  have trackerEq : input.tracker=CurrentCallResourceAsMutReturn.postTracker done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed:=by
    exact Option.some.inj (input.tracked.symm.trans (preserved.2.1.trans returned.tracked))
  have mode : input.tracker.retagMode=.Default:=by rw [trackerEq];exact seed.mode
  let next:=tracker_window trackerEq.symm current
  have nextAllocation : next.allocation=current.allocation:=tracker_allocation _ _
  have nextRuntime : DuplicatePrefixBorrowContract.RuntimeFacts next.allocation.extra input.tracker.global:=by
    rw [nextAllocation,trackerEq];exact currentRuntime
  have nextDistinct : next.allocation.extra.roots.toList.Nodup:=by rw [nextAllocation];exact distinct
  have nextShort : next.allocation.extra.nodes.size<65536:=by rw [nextAllocation];exact short
  have nextConcrete : next.pointer.value.provenance=.concrete id seed.output.tag:=by
    rw [show next.pointer=current.pointer from tracker_pointer _ _];exact concrete
  have nextEntry : entry.allocation=next.allocation:=entryEq.trans nextAllocation.symm
  obtain ⟨guardMachine,copied,machine,copyTrace,guardPreserved,copiedLive,bytes,length,tree,snapshot,physical,memory,tracked,user,race,fixed,actor⟩:=
    CurrentCallResourceCopyGuard.run options limits remaining span #[] frame post _ _ count input next entry live nextEntry
      nextRuntime nextDistinct nextShort seed.output.tag nextConcrete data profileNow done.base cached positive within statementFuel statementEq
      mode bounded rfl (by
        exact congrArg (Scalar.fromPointer (config options (remaining+1) span).access.runtime.base)
          (congrArg (Pointer.new (Provenance.concrete id seed.output.tag)) (congrArg Size.ofBytes (UInt64.add_assoc done.base (UInt64.ofNat offset) count))))
  let oldModel:=CurrentCallResourceAsMutFacts.model done fresh valid15 seed returned
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
    defaultTracker:=⟨_,tracked.trans (congrArg some trackerEq),by exact seed.mode⟩
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
    ?_,copiedLive,?_,?_,?_,?_,physical,?_,finalModel,?_,finalAddresses,finalExtras,actor,memory⟩
  · intro index bound
    exact (projections.2.2.2.2.2.2.2.2.2.2.2.2 index (by omega)).trans (keep index (.inl bound))
  · change copied.byteSize=done.entry.allocation.byteSize at bytes
    exact bytes.trans (congrArg Allocation.byteSize seed.allocationEq.symm)
  · change copied.len=done.entry.allocation.len at length
    exact length.trans (congrArg Allocation.len seed.allocationEq.symm)
  · change AllocationCopy.snapshot copied=_ at snapshot
    have sameSnapshot : AllocationCopy.snapshot entry.allocation=AllocationCopy.snapshot done.current.allocation:=by
      change AllocationCopy.snapshot (done.entry.allocation.setExtra _)=_
      exact (AllocationCopy.set_extra_preserves_storage done.entry.allocation _).2.2.2.2.2.2.trans
        (congrArg AllocationCopy.snapshot seed.allocationEq.symm)
    have sameLength : entry.allocation.len=done.current.allocation.len:=by
      change done.entry.allocation.len=_
      exact congrArg Allocation.len seed.allocationEq.symm
    rw [sameSnapshot,sameLength] at snapshot
    exact snapshot
  · simpa only [entry,Allocation.setExtra,Allocation.mapExtra,trackerEq] using tree
  · exact tracked.trans (congrArg some trackerEq)
  · rw [finalTypes]
    exact CurrentCallResourceAsMutFacts.origins done fresh valid15 seed returned

end
end DuplicatePrefix.CurrentCallResourceCopyPrefix
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceCopyPrefix" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual resource copy prefix dependency {dependency}"
