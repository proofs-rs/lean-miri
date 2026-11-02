import duplicate_prefix.CurrentCallResourceSourceCopy
import duplicate_prefix.CurrentCallSourceInstallState
import duplicate_prefix.CurrentCallResourceSourceKeyOrigin

namespace DuplicatePrefix.CurrentCallResourceSourceState
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open GeneralBorrowFnEntryRegistration TypedBorrowSteps ReferenceBorrowDriver
open CanonicalConfigFacts ActualReferenceContext CurrentCallTypedFnEntry CurrentCallResourceNormalization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
noncomputable section

/-- The SAME actual scoped source copy retains the complete finite machine
state and global tag high-water facts, ready for the return-role consumer.
All constructor/key/root certificates are derived internally. -/
theorem invoke
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : Context options remaining span) (before : Before) (tracker : MachineHooks.BorrowState)
    (data : Identities) (owner : Nat) (id : AllocId) (offset : Nat) (len : UInt64)
    (W : UniformWindow before tracker data owner id offset len.toNat .mut)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (highwater : ∀ row ∈ before.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra
      tracker.global.protectedTags tracker.global.nextPointerTag)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (binding : CandidateCallBindings.WindowBinding before W.pointer.value id offset len.toNat)
    (positive : 0<len.toNat) (signedFits : len.toNat<9223372036854775808)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (distinct : W.allocation.extra.roots.toList.Nodup) (short : W.allocation.extra.nodes.size<65536)
    (nodeRoom : W.allocation.extra.nodes.size+1≤4294967295) (race : before.dataRace=none)
    (nullComparator : ProjectionMetadataFacts.NullComparator) (dynamicFuel validationFuel : Nat)
    (fuelEq : options.place.dynamicFuel=dynamicFuel+1) (validationEq : options.limits.validation=validationFuel+1)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame before)).metadata=PreparedReflection.actual.runtime)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame before)))
    (debugOff : options.place.debugAssertions=false) (ghostOff : before.user.payload.ghost=false)
    (shallow : before.user.payload.validation=.Shallow)
    (localId : MIR.LocalId) (valid : localId<frame.locals.size) (old : Immediate Provenance)
    (live : frame.locals[localId].value=.live (.immediate old))
    (cached : frame.locals[localId].layout=some ActualReferenceMetadata.reference) (noClocks : frame.extra.dataRace=none) :
    ∃ (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex),
    let copied := CurrentCallTypedSourceCopy.copiedFrame options remaining span frame localId valid W.pointer.value len
    let validCopied : localId<copied.locals.size := by simpa only [copied,CurrentCallTypedSourceCopy.copiedFrame,Array.size_set] using valid
    let doneFrame := CurrentCallTypedSourceCopy.writtenFrame options remaining span copied borrowFrame localId validCopied W.pointer.value len id tracker.global.nextPointerTag
    let finalMachine := CurrentCallTypedSourceCopy.validated before tracker room id entry output.child.tree
    let scopedMachine := {finalMachine with borrowTracker:=some ⟨output.global,tracker.retagMode⟩}
    before.memory.live.find? (fun row=>row.1==id)=some (id,entry) ∧ entry.allocation=W.allocation ∧
    CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global borrowFrame id W.pointer.value.provenance (UInt64.ofNat offset) len=.ok output ∧
    output.tag=tracker.global.nextPointerTag ∧ output.global=(registered tracker.global borrowFrame id room).1 ∧
    output.frame=(registered tracker.global borrowFrame id room).2 ∧
    Nonempty (CurrentCallResourceFnEntry.BorrowWitness W output child (UInt64.ofNat offset) len) ∧
    ValidityMachine.validateRuntime (config options remaining span).validity () options.limits.validation
      (LocalPlaces.localRuntimePlace frames.size copied localId ActualReferenceMetadata.reference) true
      (Storage.withCurrent frames copied (ScopedFrame.entered before tracker .FnEntry))=.ok () (Storage.withCurrent frames doneFrame finalMachine) ∧
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span W.pointer.value len).imm,ActualReferenceMetadata.reference⟩
      (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView
      (Storage.withCurrent frames frame (ScopedFrame.entered before tracker .FnEntry))=.ok () (Storage.withCurrent frames doneFrame finalMachine) ∧
    MachineHooks.withRetagMode .FnEntry
      ((ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
        ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span W.pointer.value len).imm,ActualReferenceMetadata.reference⟩
        (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView)
      (Storage.withCurrent frames frame before)=.ok () (Storage.withCurrent frames doneFrame scopedMachine) ∧
    scopedMachine.borrowTracker=some ⟨output.global,tracker.retagMode⟩ ∧
    scopedMachine.memory.live.find? (fun row=>row.1==id)=some (id,{entry with allocation:=entry.allocation.setExtra output.child.tree}) ∧
    SpatialDelegation scopedMachine ⟨output.global,tracker.retagMode⟩ id (W.allocation.setExtra output.child.tree)
      (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) child ∧
    doneFrame.extra.borrowTracker=some output.frame ∧ doneFrame.returnPlace=frame.returnPlace ∧
    doneFrame.returnContinuation=frame.returnContinuation ∧ doneFrame.vaList=frame.vaList ∧
    doneFrame.body=frame.body ∧ doneFrame.bodyIdentity=frame.bodyIdentity ∧ doneFrame.functionInstance=frame.functionInstance ∧
    doneFrame.location=frame.location ∧ doneFrame.extra.dataRace=none ∧ doneFrame.locals.size=frame.locals.size ∧
    doneFrame.locals[localId]?.map (·.value)=some (.live (.immediate
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (CurrentCallResourceFnEntry.child_pointer W output.tag child).value len ActualReferenceMetadata.reference).imm)) ∧
    scopedMachine.user.payload.ghost=false ∧ DuplicatePrefixTypeCacheOrigins.Origins scopedMachine.user.payload.payload.user.types ∧
    scopedMachine.user.payload.payload.user.types=before.user.payload.payload.user.types ∧
    scopedMachine.user.addresses=before.user.addresses ∧ scopedMachine.threads=before.threads ∧ scopedMachine.dataRace=before.dataRace ∧
    DuplicatePrefixRuntimeInput.State scopedMachine ⟨output.global,tracker.retagMode⟩ ∧
    (∀ row∈scopedMachine.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra
      output.global.protectedTags output.global.nextPointerTag) := by
  obtain ⟨entry,output,child,sourceLive,allocationEq,actual,tag,global,callFrame,witnessNonempty,checked,copy,scopedResult,tracked,
    installedLive,childIssued,frameBorrowed,returnPlace,returnContinuation,varargs,frameBody,identity,callee,location,clocks,
    frameSize,localValue,ghost,postOrigins,types,addresses,threads,dataRace⟩ :=
    CurrentCallResourceSourceCopy.invoke options limits remaining span ctx before tracker data owner id offset len W runtime state highwater
      frames frame borrowFrame frameBorrow binding positive signedFits room distinct short nodeRoom race nullComparator dynamicFuel validationFuel
      fuelEq validationEq metadata origins debugOff ghostOff shallow localId valid old live cached noClocks
  obtain ⟨witness⟩ := witnessNonempty
  let finalMachine := CurrentCallTypedSourceCopy.validated before tracker room id entry output.child.tree
  let post := {finalMachine with borrowTracker:=some ⟨output.global,tracker.retagMode⟩}
  let next : MachineHooks.BorrowState := ⟨output.global,tracker.retagMode⟩
  obtain ⟨boundEntry,base,boundLive,address,length,addressFits,sourceBounds,addressEq,nonnull,provenance⟩ := binding
  have entryEq : boundEntry=entry := (Prod.mk.inj (Option.some.inj (boundLive.symm.trans sourceLive))).2
  subst boundEntry
  have offsetFits : offset<2^64 := by omega
  have startEq : (UInt64.ofNat offset).toNat=offset := by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt offsetFits]
  have bounds : (UInt64.ofNat offset).toNat+len.toNat≤W.allocation.extra.locations.size.bytes.toNat := by
    rw [startEq,W.issued.capability.treeExtent,←W.issued.capability.extent,←allocationEq]
    exact sourceBounds
  have nonzero : len≠0 := by intro zero;rw [zero] at positive;cases positive
  have keys := CurrentCallResourceSourceKeyOrigin.operation W runtime state highwater borrowFrame room (by simp [demandOf])
    distinct short nodeRoom (UInt64.ofNat offset) len startEq rfl nonzero bounds output actual
  have roots := CurrentCallResourceSourceKeyOrigin.roots W runtime state highwater borrowFrame room (by simp [demandOf])
    distinct short nodeRoom (UInt64.ofNat offset) len startEq rfl nonzero bounds output actual
  have capacity : output.child.tree.locations.size=entry.allocation.extra.locations.size := by
    rw [allocationEq]
    exact witness.capacity
  have keyOrigin : ∀ key index,(key,index)∈output.child.tree.tagMapping.mapping → key=tracker.global.nextPointerTag ∨
      ∃ oldIndex,(key,oldIndex)∈entry.allocation.extra.tagMapping.mapping := by
    rw [allocationEq]
    exact keys
  have memory : post.memory.live=(before.memory.live.filter (fun row=>row.1!=id)).push
      (id,{entry with allocation:=entry.allocation.setExtra output.child.tree}) := rfl
  obtain ⟨postState,postHighwater⟩ := CurrentCallSourceInstallState.install before post tracker next state highwater id entry sourceLive
    borrowFrame room global output.child.tree witness.runtime roots capacity keyOrigin tracked memory
  exact ⟨entry,output,child,sourceLive,allocationEq,actual,tag,global,callFrame,⟨witness⟩,checked,copy,scopedResult,tracked,
    installedLive,childIssued,frameBorrowed,returnPlace,returnContinuation,varargs,frameBody,identity,callee,location,clocks,
    frameSize,localValue,ghost,postOrigins,types,addresses,threads,dataRace,postState,postHighwater⟩

end
end DuplicatePrefix.CurrentCallResourceSourceState
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceSourceState" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual scoped source state dependency {dependency}"
