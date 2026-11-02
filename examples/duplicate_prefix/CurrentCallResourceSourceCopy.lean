import duplicate_prefix.CurrentCallTypedResourceEntry
import duplicate_prefix.CurrentCallTypedSourceCopy

namespace DuplicatePrefix.CurrentCallResourceSourceCopy
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open GeneralBorrowFnEntryRegistration TypedBorrowSteps ReferenceBorrowDriver
open CanonicalConfigFacts ActualReferenceContext CurrentCallTypedFnEntry CurrentCallResourceNormalization
open GeneralBorrowExposedNonleafPrimaryPath
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
noncomputable section

/-- One issued finite source witness supplies the actual validation, argument
copy, scoped installation, and post-world child issuance. No operation status
or transient denotation is required from the caller. -/
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
    scopedMachine.user.addresses=before.user.addresses ∧ scopedMachine.threads=before.threads ∧ scopedMachine.dataRace=before.dataRace := by
  obtain ⟨entry,base,sourceLive,address,length,addressFits,sourceBounds,addressEq,nonnull,provenance⟩ := binding
  have present : Present (ActualWorld before) id entry.allocation := by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(id,entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some sourceLive),rfl⟩
  have worldIds : ((ActualWorld before).toList.map Prod.fst).Nodup := by
    simpa [ActualWorld,List.map_map,Function.comp_def] using state.allocationIds
  have allocationEq := CandidateCurrentUniformOwnerWindow.same_id (ActualWorld before).toList worldIds id entry.allocation W.allocation present W.present
  have offsetFits : offset<2^64 := by omega
  have startEq : (UInt64.ofNat offset).toNat=offset := by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt offsetFits]
  have bounds : (UInt64.ofNat offset).toNat+len.toNat≤W.allocation.extra.locations.size.bytes.toNat := by
    rw [startEq,W.issued.capability.treeExtent,←W.issued.capability.extent,←allocationEq]
    exact sourceBounds
  have nonzero : len≠0 := by intro zero;rw [zero] at positive;cases positive
  obtain ⟨output,child,actual,tag,global,callFrame,readDone,childDone,lookup,witnessNonempty⟩ :=
    CurrentCallResourceFnEntry.correlated_borrow W runtime state highwater borrowFrame room (by simp [demandOf]) distinct short nodeRoom
      (UInt64.ofNat offset) len startEq rfl nonzero bounds
  obtain ⟨witness⟩ := witnessNonempty
  have sourceBinding : CandidateCallBindings.WindowBinding before W.pointer.value id offset len.toNat :=
    ⟨entry,base,sourceLive,address,length,addressFits,sourceBounds,addressEq,nonnull,provenance⟩
  have actualEntry : CandidateCurrentFnEntryRaw.operation entry.allocation.extra tracker.global borrowFrame id W.pointer.value.provenance (UInt64.ofNat offset) len=.ok output := by
    rw [allocationEq];exact actual
  obtain ⟨checked,copy,scopedResult,tracked,installedLive,frameBorrowed,frameSize,localPair,ghost,types,addresses,threads,dataRace⟩ :=
    CurrentCallTypedSourceCopy.validate_copy_of_typed_operation options limits remaining span ctx before tracker frames frame borrowFrame state.enabled frameBorrow
      W.pointer.value id offset len entry sourceLive sourceBinding positive signedFits room race nullComparator dynamicFuel validationFuel fuelEq validationEq metadata origins
      debugOff ghostOff shallow output actualEntry readDone childDone localId valid old live cached noClocks
  let copied := CurrentCallTypedSourceCopy.copiedFrame options remaining span frame localId valid W.pointer.value len
  have validCopied : localId<copied.locals.size := by simpa only [copied,CurrentCallTypedSourceCopy.copiedFrame,Array.size_set] using valid
  let doneFrame := CurrentCallTypedSourceCopy.writtenFrame options remaining span copied borrowFrame localId validCopied W.pointer.value len id tracker.global.nextPointerTag
  let finalMachine := CurrentCallTypedSourceCopy.validated before tracker room id entry output.child.tree
  let post := {finalMachine with borrowTracker:=some ⟨output.global,tracker.retagMode⟩}
  let next : MachineHooks.BorrowState := ⟨output.global,tracker.retagMode⟩
  have present : Present (ActualWorld post) id (W.allocation.setExtra output.child.tree) := by
    simp only [Present,ActualWorld,Array.toList_map]
    have member := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some installedLive)
    apply List.mem_map.mpr
    refine ⟨(id,{entry with allocation := entry.allocation.setExtra output.child.tree}),member,?_⟩
    simp only [allocationEq]
  have rootTag : next.global.rootTag? id = tracker.global.rootTag? id := by rw [show next.global = output.global from rfl,global];rfl
  have vacant : W.allocation.extra.nodes.get child = none := by
    cases oldAt : W.allocation.extra.nodes.get child with
    | none => rfl
    | some old =>
      obtain ⟨changed,changedAt,changedTag,_,_,_⟩ := witness.oldNodes child old oldAt
      have same : changed = witness.node := Option.some.inj (changedAt.symm.trans witness.nodeAt)
      have oldTag : old.tag = output.tag := changedTag.symm.trans ((congrArg TreeNode.tag same).trans witness.tag)
      have older := GeneralBorrowParentTagInvariant.parent_below_fresh W.allocation.extra tracker.global runtime child old oldAt
      rw [oldTag,tag] at older
      exact False.elim (Nat.lt_irrefl _ (UInt64.lt_iff_toNat_lt.mp older))
  have parentIssued := CurrentCallResourceInstallation.spatial W.issued W.parents post next output.child.tree present rootTag
    witness.capacity witness.oldRoots witness.oldNodes child W.pointer.grant vacant
  have childIssued : SpatialDelegation post next id (W.allocation.setExtra output.child.tree)
      (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) child := by
    have shape := witness.constructor
    cases provenance : W.pointer.value.provenance with
    | concrete supplied tag =>
      rw [provenance] at shape
      obtain ⟨parent,parentAt,_,_⟩ := W.binding
      obtain ⟨current,currentAt,_,_,_,_⟩ := witness.oldNodes W.pointer.grant parent parentAt
      apply SpatialDelegation.concrete parentIssued
      exact .step (.refl W.pointer.grant current currentAt) witness.node witness.nodeAt shape
    | wildcard =>
      rw [provenance] at shape
      obtain ⟨position,root,rootNode,rootSlot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path output.child.tree witness.parents.graph child witness.node witness.nodeAt
      have rootEq : root = child := by
        cases path with
        | refl => rfl
        | @step predecessor target earlier node found edge =>
          have same : node = witness.node := Option.some.inj (found.symm.trans witness.nodeAt)
          rw [same,shape] at edge
          cases edge
      subst root
      have edge := S05ConcreteProtectedChildCompletion.child_edge W.precise.completion child W.pointer.grant
      obtain ⟨earlier,originRoot,newRoot,originNode,before,originSlot,newRootAt,originAt,exposed,older,originPath⟩ :=
        witness.parents.virtual position child rootSlot W.pointer.grant edge
      have same : newRoot = witness.node := Option.some.inj (newRootAt.symm.trans witness.nodeAt)
      exact SpatialDelegation.wildcard originNode newRoot earlier position originRoot parentIssued originAt exposed newRootAt
        (by rw [same];exact shape) older before originSlot rootSlot originPath edge
  have localValue : doneFrame.locals[localId]?.map (·.value)=some (.live (.immediate
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (CurrentCallResourceFnEntry.child_pointer W output.tag child).value len ActualReferenceMetadata.reference).imm)) := by
    simpa only [CurrentCallTypedSourceCopy.value,CurrentCallResourceFnEntry.child_pointer,changedPointer,tag,Pointer.new] using localPair
  refine ⟨entry,output,child,sourceLive,allocationEq,actual,tag,global,callFrame,⟨witness⟩,checked,copy,scopedResult,rfl,
    installedLive,childIssued,frameBorrowed,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,frameSize,localValue,ghost,origins,types,addresses,threads,dataRace⟩
  exact noClocks

end
end DuplicatePrefix.CurrentCallResourceSourceCopy
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceSourceCopy" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved issued source copy dependency {dependency}"
