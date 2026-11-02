import duplicate_prefix.GeneralBorrowForestCopyRootGuardBody
import duplicate_prefix.GeneralBorrowForestCopyReleaseData
import duplicate_prefix.GeneralBorrowForestAcceptedPhysicalExit
import duplicate_prefix.CopyRootExitData

namespace DuplicatePrefix.GeneralBorrowForestCopyReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Concurrency
open PhysicalMachineWrite
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

set_option autoImplicit false in
/-- The pre-copy root state and physical return-slot data. All fields describe
input values, metadata, allocation contents or fixed configuration. -/
structure Input where
  options : EvalConfigurationCore.Options
  limits : ExecutionMachine.Limits
  remaining : Nat
  span : PreparedContracts.FixedSpanQuery
  before : CompilerFrameContext.ActualFrame
  caller : CompilerFrameContext.ActualFrame
  machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser
  pointer : Scalar Provenance
  destinationValue : Scalar Provenance
  count : UInt64
  entry : CopyRootEntry.Input options limits remaining span #[] caller machine pointer destinationValue count
  data : GeneralBorrowForestCopyRootGuardBody.CopyData options remaining span machine entry.tracker pointer destinationValue count
  statementFuel : limits.validation = entry.fuel+1
  defaultMode : entry.tracker.retagMode = .Default
  context : Context
  validationContext : Context
  accessEq : (PreparedContracts.actualConfig options () remaining span).access = validationContext.access
  validationWidth : validationContext.pointers.arithmetic = ⟨Size.ofBytes 8⟩
  validationRuntimeSize : validationContext.access.runtime.pointerSize = Size.ofBytes 8
  sameRuntime : validationContext.access.runtime.base = context.access.runtime.base
  width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩
  runtimeWidth : context.access.runtime.base.pointerWidth = .w64
  runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8
  outerAccessEq : (PreparedContracts.actualConfig options () (remaining+1) span).access = context.access
  shape : PositiveRootSuccessProfile.FrameShape before caller pointer destinationValue count
  zero : before.locals[0]? = some ⟨.live (.immediate .uninit),none⟩
  body : before.body = RootBody.reflected.body.body
  identity : before.bodyIdentity = RootBody.reflected.body.identity
  callee : before.functionInstance = RootBody.reflected.functionInstance
  noLocalClocks : before.extra.dataRace = none
  continuation : before.returnContinuation = .stop true
  varargs : before.vaList = #[]
  slotId : AllocId
  separate : slotId ≠ data.id
  slot : LocalAllocation Provenance BorrowTree MiriMemoryKind
  slotPresent : machine.memory.live.find? (fun row => row.1 == slotId) = some (slotId,slot)
  slotRoot : BorTag
  slotChild : BorTag
  slotTree : slot.allocation.extra = slotTree slotRoot slotChild 1 true
  slotRootFree : entry.tracker.global.protectedTags.contains slotRoot = false
  slotChildHeld : entry.tracker.global.protectedTags.contains slotChild = true
  slotDistinct : slotRoot ≠ slotChild
  release : GeneralBorrowForestCopyReleaseData.Input data.allocation.extra entry.tracker.global.protectedTags data.tag data.offset data.sliceLen count
  releaseTag : BorTag
  releaseNode : TreeNode
  releaseNodePresent : data.allocation.extra.nodeAt release.target = some releaseNode
  releaseNotExposed : releaseNode.isExposed = false
  releaseTagPresent : data.allocation.extra.indexOfTag releaseTag = some release.target
  frameTracked : before.extra.borrowTracker = some
    ((({} : FrameState).addProtector data.id releaseTag).addProtector slotId slotChild)
  slotSize : slot.allocation.byteSize = Size.ofBytes 1
  slotStorage : slot.allocation.len = 1
  slotMask : slot.allocation.initializationMask = InitMask.new (Size.ofBytes 1) false
  slotProvenance : slot.allocation.provenanceMap = ProvenanceMap.new
  slotMutable : slot.allocation.mutability = .Mut
  place : MPlaceTy Provenance
  layout : place.layout = RootCompilerFacts.boolLayout
  slotBase : UInt64
  slotPointer : place.mplace.ptr = Pointer.new (some (.concrete slotId slotRoot)) (Size.ofBytes slotBase)
  aligned : place.mplace.misaligned = none
  fits : slotBase.toNat + 1 < 2^64
  cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == slotId) = some ⟨slotId,slotBase⟩
  extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == slotId) = some (slotId,⟨none,#[]⟩)
  destination : before.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩


def Result (input : Input) : Prop :=
  let config := PreparedContracts.actualConfig input.options () (input.remaining+1) input.span
  let initial := Storage.withCurrent #[] input.caller input.machine
  let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit := ⟨config,input.limits,fun _ _ => True⟩
  ∃ finalState updated,
    SuccessfulTrace.Trace config input.limits initial finalState ∧
    ExecutionMachine.step config input.limits () finalState = (finalState,.ok false) ∧
    CallSafety.NoUBBeforeReturn safety 1 initial ∧
    finalState.stack.frames = #[] ∧
    finalState.machine.memory.live.find? (fun row => row.1 == input.slotId) = some (input.slotId,⟨input.slot.kind,updated⟩) ∧
    updated.extra = parentWrittenTree input.slotRoot input.slotChild 1 ∧
    updated.byteSize = input.slot.allocation.byteSize ∧ updated.len = input.slot.allocation.len ∧
    updated.initializationMask = InitMask.new input.slot.allocation.byteSize true ∧
    updated.provenanceMap = ProvenanceMap.new ∧
    target_bytes input.context.access.runtime.base input.slot.allocation.byteSize 1 = .ok (AllocationCopy.snapshot updated) ∧
    updated.mutability = input.slot.allocation.mutability

private theorem slice_positive (offset len count capacity : UInt64)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat) (twice : count.toNat+count.toNat ≤ len.toNat)
    (positive : (0 : UInt64) < count) : offset.toNat < (offset+len).toNat := by
  have capacityFits : capacity.toNat < 2^64 := UInt64.toNat_lt_size capacity
  have fits : offset.toNat+len.toNat < 2^64 := by omega
  have countPositive := UInt64.lt_iff_toNat_lt.mp positive
  simp only [UInt64.toNat_zero] at countPositive
  simp only [UInt64.toNat_add,Nat.mod_eq_of_lt fits]
  omega

/-- Run the actual guards/copy, recover the root's older mutable protector,
release the real two-row frame and physically return true. Every operation
success is derived internally from data-only ownership/activity contracts. -/
theorem complete (input : Input) : Result input := by
  obtain ⟨copied,machine,copyTrace,lookup,bytes,len,tree,snapshot,memory,tracked,race,ghost,shallow,unchecked,noGc,fixed,
      addresses,types,backend,extras,copyOwned,copyWell,copyCapacity,thread,active⟩ := GeneralBorrowForestCopyRootGuardBody.complete
    input.options input.limits input.remaining input.span #[] input.caller input.machine input.pointer input.destinationValue input.count
    input.entry input.statementFuel input.defaultMode input.data
  have info := GeneralBorrowForestCopyReleaseData.after_copy input.data.allocation.extra input.entry.tracker.global.protectedTags
    input.data.tag input.data.offset input.data.sliceLen input.count input.release
  have metadata : copied.extra = {input.data.allocation.extra with locations := copied.extra.locations} := by rw [tree];exact info.1
  have nodes : copied.extra.nodes = input.data.allocation.extra.nodes := congrArg (fun tree => tree.nodes) metadata
  have releaseOwned : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestMutableAccess.Data copied.extra location input.entry.tracker.global.protectedTags
        input.release.target input.release.copy.primary input.release.copy.extras))
      input.data.offset (input.data.offset+input.data.sliceLen) copied.extra.locations := by rw [tree];exact info.2.1
  have releaseActive : GeneralBorrowFreshReleaseLoop.ActiveOn copied.extra input.release.target .Write
      input.data.offset (input.data.offset+input.data.sliceLen) := by rw [tree];exact info.2.2.2
  have slotPresent : machine.memory.live.find? (fun row => row.1 == input.slotId) = some (input.slotId,input.slot) := by
    rw [memory,CopyRootExitData.memory_after_eq_commit]
    exact StackPopRelease.lookup_commit_other input.machine.memory input.data.id input.slotId
      ⟨input.data.kind,copied⟩ input.slot copied.extra input.separate input.slotPresent
  let release : GeneralBorrowForestPhysicalReturnPlan.Input machine.memory input.entry.tracker.global.protectedTags := {
    id := input.data.id,tag := input.releaseTag,buffer := ⟨input.data.kind,copied⟩,present := lookup
    anchor := input.release.target,primary := input.release.copy.primary,extras := input.release.copy.extras
    context := by
      rw [metadata]
      exact GeneralBorrowForestForeignSliceRepeated.context_on_map input.data.allocation.extra _ input.release.target
        input.release.copy.primary input.release.copy.extras input.release.targetContext
    lower := input.data.offset,upper := input.data.offset+input.data.sliceLen
    positive := slice_positive input.data.offset input.data.sliceLen input.count input.data.allocation.extra.locations.size.bytes
      input.release.copy.bounds input.release.copy.twice input.data.positive
    fits := by rw [nodes];exact input.release.copy.fits
    tagPresent := by rw [metadata];exact input.releaseTagPresent
    active := releaseActive,owned := releaseOwned
    slotId := input.slotId,separate := input.separate,slot := input.slot,slotPresent := slotPresent
    slotRoot := input.slotRoot,slotChild := input.slotChild,slotTree := input.slotTree
    slotRootFree := input.slotRootFree,slotChildHeld := input.slotChildHeld,slotDistinct := input.slotDistinct }
  let exit : GeneralBorrowForestAcceptedPhysicalExit.Input := {
    options := input.options,limits := input.limits,remaining := input.remaining,span := input.span
    source := input.entry.source,fuel := input.entry.fuel,debugOff := input.entry.debug,validationFuel := input.entry.validationFuel
    context := input.context,validationContext := input.validationContext,accessEq := input.accessEq
    validationWidth := input.validationWidth,validationRuntimeSize := input.validationRuntimeSize,sameRuntime := input.sameRuntime
    width := input.width,runtimeWidth := input.runtimeWidth,runtimeSize := input.runtimeSize,outerAccessEq := input.outerAccessEq
    before := input.before,ready := CopyRootOutput.caller input.caller input.entry.valid
    pointer := input.pointer,destinationValue := input.destinationValue,count := input.count
    shape := CopyRootSuccessShape.of_copy input.before input.caller input.pointer input.destinationValue input.count input.shape input.zero input.entry.valid
    body := input.body,identity := input.identity,callee := input.callee,noLocalClocks := input.noLocalClocks
    continuation := input.continuation,varargs := input.varargs
    machine := machine,tracker := input.entry.tracker,tracked := tracked,defaultMode := input.defaultMode
    noClocks := race,noBackend := backend.trans input.entry.backend,ghost := ghost,shallow := shallow
    unchecked := unchecked,noGc := noGc,fixed := fixed,thread := thread,active := active,release := release
    frameTracked := input.frameTracked,slotSize := input.slotSize,slotStorage := input.slotStorage,slotMask := input.slotMask
    slotProvenance := input.slotProvenance,slotMutable := input.slotMutable,place := input.place,layout := input.layout
    slotBase := input.slotBase,slotPointer := input.slotPointer,aligned := input.aligned,fits := input.fits
    cached := by rw [addresses];exact input.cached
    extras := by
      change machine.user.payload.payload.user.runtime.extras.allocations.find? _ = _
      rw [extras]
      exact input.extras
    destination := input.destination }
  obtain ⟨updated,returnTrace,terminated,safe,written,size,length,mask,provenance,encoding,mutable⟩ := GeneralBorrowForestAcceptedPhysicalExit.complete exit
  let done := CanonicalCopy.replaceAllocation (GeneralBorrowForestAcceptedPhysicalExit.popped exit) input.slotId input.slot.kind updated
  have full : SuccessfulTrace.Trace (PreparedContracts.actualConfig input.options () (input.remaining+1) input.span) input.limits
      (Storage.withCurrent #[] input.caller input.machine) done := SuccessfulTrace.append copyTrace returnTrace
  have safety := SuccessfulTrace.no_ub
    (⟨PreparedContracts.actualConfig input.options () (input.remaining+1) input.span,input.limits,fun _ _ => True⟩ :
      CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
    1 (Storage.withCurrent #[] input.caller input.machine) done ⟨by decide,rfl⟩ full (by change 0 < 1;decide)
  exact ⟨done,updated,full,terminated,safety,rfl,CanonicalCopy.replace_lookup _ _ _ _,written,size,length,mask,provenance,encoding,mutable⟩

end DuplicatePrefix.GeneralBorrowForestCopyReturn
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.GeneralBorrowForestCopyReturn.complete) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved generic copy physical return dependency {dependency}"
