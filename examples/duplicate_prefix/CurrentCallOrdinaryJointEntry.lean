import duplicate_prefix.CurrentCallJointEntry
import duplicate_prefix.CurrentCallOrdinaryReturnLive
import duplicate_prefix.CurrentCallConversionPlanAdequacy

/-! The adopted current-input dispatcher consumes the same joint checkpoint.
Initial LIVE/latent classification is separate from execution; the LIVE branch
uses the existing joint fixed-family spatial assembly and actual paired entry. -/
namespace DuplicatePrefix.CurrentCallOrdinaryJointEntry
open Miri Miri.ABI Miri.Input Miri.Memory Miri.MIR Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CurrentCallResourceNormalization
open CurrentCallSpatialCover CurrentCallOrdinaryInput CurrentCallFamilySatisfaction
open CanonicalConfigFacts ActualReferenceContext RootFrameData
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

private theorem binding {before tracker family offset length capacity initialized}
    (selected : SelectedPointer before tracker family offset capacity)
    (role : LiveRole before tracker family offset length capacity initialized) :
    CandidateCallBindings.WindowBinding before family.value family.allocation offset.toNat length.toNat := by
  obtain ⟨entry,live,size,physical,cap,owned⟩:=role
  obtain ⟨base,cached,range,address,nonnull,representation⟩:=selected
  have bytes : entry.allocation.len=capacity.toNat := by rw [physical.1.1,size];rfl
  refine ⟨entry,base,live,cached,physical.1.1,?_,?_,address,nonnull,?_⟩
  · rw [bytes];exact range
  · rw [physical.1.1];exact physical.2.2.1
  · cases provenance : family.value.provenance with
    | concrete id tag=>rw [provenance] at representation;exact representation.1
    | wildcard=>rw [provenance] at representation;simpa only [size] using representation

private theorem physical_slice {allocation : Allocation Provenance BorrowTree} {offset length : UInt64}
    (physical : Physical allocation offset length true) (positive : 0<length.toNat)
    (fits : length.toNat<9223372036854775808) : OrdinaryPhysicalValidity.MutU8Slice allocation offset length := by
  obtain ⟨⟨storage,maskValid,maskLength,provenance⟩,mutable,bounds,initialized⟩:=physical
  exact ⟨⟨storage,maskLength,maskValid,provenance⟩,positive,fits,bounds,mutable,initialized rfl⟩

private theorem runtime {options limits remaining span before argument len place}
    (input : OrdinaryInput options limits remaining span before argument len place)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row=>row.1==id)=some (id,entry)) :
    DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra input.tracker.global := by
  have member:=Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live)
  exact ⟨input.runtime.formed _ member,input.runtime.coherent _ member,input.runtime.possible _ member,
    input.resources.tagsBelow _ member⟩

private theorem live_of_selected {options limits remaining span before argument len place}
    (input : OrdinaryInput options limits remaining span before argument len place)
    (family : Family) (offset capacity : UInt64)
    (positive : 0<len.toNat) (fits : len.toNat<9223372036854775808)
    (encoding : argument=.pointer family.value) (assigned : input.assignment.Binds input.sourceOccurrence family)
    (charge : CurrentCallPointwiseSpatialCover.ExactCharge input.Fs input.sourceOwner .mut family.allocation offset.toNat len.toNat)
    (selected : SelectedPointer before input.tracker family offset capacity)
    (sourceRole : LiveRole before input.tracker family offset len capacity true)
    (returnRole : LiveRole before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false)
    (sourceReady : (∃entry : LocalAllocation Provenance BorrowTree MiriMemoryKind,
      before.memory.live.find? (fun row=>row.1==family.allocation)=some (family.allocation,entry))→
      CurrentCallBoolProtection.WindowReady before family.allocation offset.toNat len.toNat)
    (count : UInt64) :
    ∃checkpoint : CurrentCallPostEntryCheckpoint.Checkpoint options remaining span len count place,
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base argument len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true) (⟨⟨#[]⟩,before⟩ : RootState)=
        .ok () (Storage.withCurrent #[] checkpoint.frame checkpoint.machine) := by
  obtain ⟨packet⟩:=CurrentCallOrdinaryReturnLive.form input returnRole
  obtain ⟨sourceEntry,sourceLive,sourceSize,sourcePhysical,sourceCap,sourceOwned⟩:=sourceRole
  obtain ⟨returnEntry,returnLive,returnSize,returnPhysical,returnCap,returnOwned⟩:=returnRole
  have sourceBinding:=binding selected ⟨sourceEntry,sourceLive,sourceSize,sourcePhysical,sourceCap,sourceOwned⟩
  have returnBinding : CandidateCallBindings.WindowBinding before input.returnFamily.value input.returnFamily.allocation input.returnOffset.toNat 1 := by
    rw [←packet.familyPointer,←packet.familyId,←packet.familyOffset]
    exact packet.binding
  have sourceMember:=Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some sourceLive)
  have returnMember:=Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some returnLive)
  obtain ⟨ctx,S,R,sourceFamily,returnFamily,_,_,_,_,sourceAllocation,returnAllocation⟩:=
    CurrentCallFamilySpatialAdmission.positive_live input.assignment input.sourceOccurrence input.returnOccurrence
      argument len place positive family input.returnFamily offset.toNat input.returnOffset.toNat
      assigned input.sourceActual input.returnBound input.returnActual input.returnLayout sourceEntry returnEntry
      sourceLive returnLive sourceBinding returnBinding input.Fs input.Fr input.sourceOwner input.returnOwner
      input.composable charge input.returnCharge sourceCap returnCap (runtime input _ _ sourceLive)
      (runtime input _ _ returnLive) (input.runtime.parent_order _ _ sourceLive) (input.runtime.parent_order _ _ returnLive)
      (input.runtime.roots _ sourceMember) (input.runtime.roots _ returnMember) sourceOwned returnOwned
  have sourceId : S.backing.id=family.allocation:=S.id.symm.trans (congrArg Family.allocation sourceFamily)
  have returnId : R.backing.id=input.returnFamily.allocation:=R.id.symm.trans (congrArg Family.allocation returnFamily)
  have race:=input.model.noDataRace
  let root:=CurrentCallSpatialEntryControl.root before #[] place race
  have rawBorrow : root.frame.extra.borrowTracker=some ({} : FrameState):=
    RootEntryFrame.raw_borrow (CurrentCallPush.preparedMachine before #[]) (.memory place)
      (CallEntryFacts.freshRoot before).2 input.tracker input.runtime.enabled
  let C : CurrentCallSpatialEntry.Conditions options remaining span #[] root before input.tracker ctx
      offset.toNat len S input.returnOffset.toNat R place:={
    model:=input.model
    state:=input.runtime.toState
    highwater:=input.resources.tagsBelow
    rawLocals:=rfl
    borrowFrame:={}
    frameBorrow:=rawBorrow
    binding:=by simpa only [sourceFamily,sourceId] using sourceBinding
    positive:=positive
    signedFits:=fits
    tagRoom:=by have room:=input.resources.tagRoom;omega
    sourceRoom:=by rw [sourceAllocation];have room : sourceEntry.allocation.extra.nodes.size+16<65536:=input.resources.nodeRoom _ sourceMember;omega
    boolRoom:=by rw [returnAllocation];have room : returnEntry.allocation.extra.nodes.size+16<65536:=input.resources.nodeRoom _ returnMember;omega
    dynamicFuel:=options.place.dynamicFuel-1
    validationFuel:=options.limits.validation-1
    dynamicEq:=by have room:=packet.dynamicPositive;omega
    validationEq:=by have room:=packet.validationPositive;omega
    origins:=input.cacheOrigins
    physical:=packet.physical
    physicalId:=packet.familyId.trans returnId.symm
    physicalOffset:=congrArg UInt64.toNat packet.familyOffset
    returnPointer:=packet.familyPointer.trans (congrArg Family.value returnFamily).symm
    returnBinding:=packet.binding
    ready:=packet.ready
    separate:=by
      rw [sourceId,returnId]
      exact CurrentCallPointwiseSpatialCover.exclusive_separate input.composable charge input.returnCharge}
  have physical : OrdinaryPhysicalValidity.MutU8Slice S.backing.allocation (UInt64.ofNat offset.toNat) len := by
    rw [sourceAllocation,UInt64.ofNat_toNat]
    exact physical_slice sourcePhysical positive fits
  have profile : CurrentCallBoolProtection.WindowReady before S.backing.id offset.toNat len.toNat := by
    rw [sourceId]
    exact sourceReady ⟨sourceEntry,sourceLive⟩
  obtain ⟨checkpoint,actual⟩:=CurrentCallJointEntry.live limits race C input.stackReady physical
    (by rw [sourceAllocation];exact input.resources.storageRoom _ sourceMember) profile
    (by rw [sourceAllocation];have room : sourceEntry.allocation.extra.nodes.size+16<65536:=input.resources.nodeRoom _ sourceMember;omega)
    (by have room:=input.resources.tagRoom;omega) count
  refine ⟨checkpoint,?_⟩
  rw [encoding]
  simpa only [sourceFamily,DuplicatePrefixSliceArgument.first,DuplicatePrefixSliceArgument.rawValue,
    CurrentCallTypedSourceCopy.value] using actual

/-- Initial current-data branch selection, not a successful call predicate. -/
def sourceIsLive (before : Before) (argument : DuplicatePrefixSliceArgument.Argument) (length : UInt64) : Bool :=
  match CurrentCallConversionPlan.sourceQuery before argument length with
  | .ok (some id)=>(before.memory.live.find? (fun row=>row.1==id)).isSome
  | _=>false

/-- The BOTH-LIVE branch of the adopted domain reaches the common checkpoint
for every count. All entry conditions are derived from the declared input;
only the initial representation branch and nonempty length are selected here. -/
theorem live {options limits remaining span before argument len place}
    (input : OrdinaryInput options limits remaining span before argument len place)
    (positive : len≠0) (sourceLive : sourceIsLive before argument len=true)
    (returnLive : (before.memory.live.find? (fun row=>row.1==input.returnFamily.allocation)).isSome=true)
    (count : UInt64) :
    ∃checkpoint : CurrentCallPostEntryCheckpoint.Checkpoint options remaining span len count place,
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base argument len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true) (⟨⟨#[]⟩,before⟩ : RootState)=
        .ok () (Storage.withCurrent #[] checkpoint.frame checkpoint.machine) := by
  rcases input.source with ⟨zero,_⟩|⟨_,fits,family,offset,capacity,encoding,assigned,charge,selected,backing,ready⟩
  · exact False.elim (positive zero)
  · have query:=CurrentCallConversionPlanAdequacy.query_of_selected before input.tracker family offset capacity len true
      selected backing fits
    have sourceQuery : CurrentCallConversionPlan.sourceQuery before argument len=.ok (some family.allocation) := by
      rw [encoding]
      exact query
    have actualLive : (before.memory.live.find? (fun row=>row.1==family.allocation)).isSome=true := by
      simpa only [sourceIsLive,sourceQuery] using sourceLive
    have sourceRole : LiveRole before input.tracker family offset len capacity true := by
      rcases backing with live|latent
      · exact live
      · rw [latent.1] at actualLive
        cases actualLive
    have returnRole : LiveRole before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false := by
      rcases input.returnBacking with live|latent
      · exact live
      · rw [latent.1] at returnLive
        cases returnLive
    have nonzero : len.toNat≠0 := by
      intro zero
      exact positive (UInt64.toNat_inj.mp zero)
    exact live_of_selected input family offset capacity (by omega) fits encoding assigned charge selected sourceRole returnRole ready count

end
end DuplicatePrefix.CurrentCallOrdinaryJointEntry

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallOrdinaryJointEntry.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved adopted-domain joint entry dependency {name}: {dependency}"
