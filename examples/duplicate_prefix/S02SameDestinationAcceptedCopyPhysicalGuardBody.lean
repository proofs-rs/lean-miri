import duplicate_prefix.GeneralBorrowRawCopyRootGuardBody
import duplicate_prefix.CopyRootGuardBodyIndependentFuel
import duplicate_prefix.S02SameDestinationAcceptedCopyPhysicalRootComplete

namespace DuplicatePrefix.S02SameDestinationAcceptedCopyPhysicalGuardBody
open DuplicatePrefix.GeneralBorrowRawCopyRootGuardBody
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefix.CopyRootGuardBody
open DuplicatePrefix.CopyRootGuardBodyIndependentFuel
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option autoImplicit false in
/-- Data needed for the actual copy after the language/runtime guard returns.
Every field describes inputs, allocation contents or the fixed configuration;
no successful interpreter operation is an input field. -/
structure CopyData (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (sourcePointer destinationPointer : Scalar Provenance) (n : UInt64) where
  id : AllocId
  tag : BorTag
  base : UInt64
  offset : UInt64
  sliceLen : UInt64
  kind : MemoryKind MiriMemoryKind
  allocation : Allocation Provenance BorrowTree
  positive : 0 < n
  sliceBounds : offset.toNat + sliceLen.toNat ≤ allocation.byteSize.bytes.toNat
  copyBounds : n.toNat+n.toNat ≤ sliceLen.toNat
  storage : allocation.len = allocation.byteSize.bytes.toNat
  maskValid : InitMaskCopy.WellFormed allocation.initializationMask
  maskLen : allocation.initializationMask.len = allocation.byteSize
  initialized : InitMaskCopy.InitializedOn allocation.initializationMask (Size.ofBytes offset) (Size.ofBytes (offset+n))
  valid : S02SameDestinationUninitProvenanceInput.DirectInput allocation.provenanceMap allocation.len
  storageFits : allocation.len+64 < 18446744073709551616
  mutable : allocation.mutability = .Mut
  extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩)
  live : machine.memory.live.find? (fun row => row.1 == id) = some (id,⟨kind,allocation⟩)
  cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩
  borrow : GeneralBorrowRawCopyInput.Input allocation.extra tracker.global tag offset sliceLen n
  bounded : n ≤ (PreparedContracts.actualConfig options () (remaining+1) span).projection.maxSizeOfVal.bytes
  source : sourcePointer = Scalar.fromPointer
    (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
    (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset)))
  destination : destinationPointer = Scalar.fromPointer
    (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
    (Pointer.new (.concrete id tag) (Size.ofBytes (base+(offset+n))))

variable (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
  (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
  (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
  (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
  (sourcePointer destinationPointer : Scalar Provenance) (n : UInt64)
  (input : CopyRootEntry.Input options limits remaining span frames caller machine sourcePointer destinationPointer n)

private theorem returned_slots (sourcePointer destinationPointer : Scalar Provenance) (n : UInt64)
    (xs : Array (LocalState Provenance LocalLayout))
    (rows : xs = #[⟨.live (.immediate .uninit),none⟩,
        ⟨.live (.immediate (.scalar sourcePointer)),some CopyCompilerFacts.sourcePointerLayout⟩,
        ⟨.live (.immediate (.scalar destinationPointer)),some CopyCompilerFacts.destPointerLayout⟩,
        ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩,
        ⟨.live (.immediate .uninit),none⟩,
        ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩] ++
        Array.replicate 11 ⟨.dead,none⟩) :
    ∃ (v0 : (0 : MIR.LocalId) < xs.size) (v1 : (1 : MIR.LocalId) < xs.size) (v2 : (2 : MIR.LocalId) < xs.size) (v3 : (3 : MIR.LocalId) < xs.size) (v4 : (4 : MIR.LocalId) < xs.size) (v5 : (5 : MIR.LocalId) < xs.size) (v14 : (14 : MIR.LocalId) < xs.size) (v15 : (15 : MIR.LocalId) < xs.size) (v16 : (16 : MIR.LocalId) < xs.size),
      xs[0]'v0 = ⟨.live (.immediate .uninit),none⟩ ∧
      xs[1]'v1 = ⟨.live (.immediate (.scalar sourcePointer)),some CopyCompilerFacts.sourcePointerLayout⟩ ∧
      xs[2]'v2 = ⟨.live (.immediate (.scalar destinationPointer)),some CopyCompilerFacts.destPointerLayout⟩ ∧
      xs[3]'v3 = ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩ ∧
      xs[4]'v4 = ⟨.live (.immediate .uninit),none⟩ ∧
      xs[5]'v5 = ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      xs[14]'v14 = ⟨.dead,none⟩ ∧
      xs[15]'v15 = ⟨.dead,none⟩ ∧
      xs[16]'v16 = ⟨.dead,none⟩ := by
  subst xs
  exact ⟨by change 0 < 17; decide,by change 1 < 17; decide,by change 2 < 17; decide,by change 3 < 17; decide,by change 4 < 17; decide,by change 5 < 17; decide,by change 14 < 17; decide,by change 15 < 17; decide,by change 16 < 17; decide,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Execute the real root copy call, both guards, and the copy helper return.
The previously internal guard-prefix premise is discharged by `from_copy`. -/
theorem complete
    (statementBudget : Nat) (statementFuel : limits.validation = statementBudget+1)
    (mode : input.tracker.retagMode = .Default)
    (data : S02SameDestinationAcceptedCopyPhysicalGuardBody.CopyData options remaining span machine input.tracker sourcePointer destinationPointer n) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let readAccess := data.allocation.extra.performBorrowAccessRange (.concrete data.tag)
      (Size.ofBytes data.offset) (Size.ofBytes n) .Read input.tracker.global.protectedTags .VisitChildrenOfAccessed
    let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete data.tag)
      (Size.ofBytes (data.offset+n)) (Size.ofBytes n) .Write input.tracker.global.protectedTags .VisitChildrenOfAccessed
    ∃ result finalMachine,
      SuccessfulTrace.Trace config limits (Storage.withCurrent frames caller machine)
        (Storage.withCurrent frames (CopyRootOutput.caller caller input.valid) finalMachine) ∧
      finalMachine.memory.live.find? (fun row => row.1 == data.id) = some (data.id,⟨data.kind,result⟩) ∧
      result.byteSize = data.allocation.byteSize ∧ result.len = data.allocation.len ∧ result.extra = writeAccess.tree ∧
      AllocationCopy.snapshot result = (AllocationCopy.snapshot data.allocation).extract 0 (data.offset+n).toNat ++
        (AllocationCopy.snapshot data.allocation).extract data.offset.toNat (data.offset+n).toNat ++
        (AllocationCopy.snapshot data.allocation).extract (data.offset+n+n).toNat data.allocation.len ∧
      finalMachine.memory = CopyHelperCall.memoryAfter machine.memory data.id data.kind result ∧
      finalMachine.borrowTracker = some input.tracker ∧
      finalMachine.dataRace = none ∧ finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      (config.terminators.getControl finalMachine.user).checkedArithmetic = false ∧
      (config.terminators.getControl finalMachine.user).gcInterval = 0 ∧ finalMachine.threads.fixedScheduling = true ∧
      finalMachine.user.addresses = machine.user.addresses ∧
      finalMachine.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      finalMachine.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      finalMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      DuplicatePrefixBorrowContract.RuntimeFacts result.extra input.tracker.global ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive result.extra input.tracker.global.protectedTags
        (some data.borrow.anchor) (some data.borrow.selected) data.borrow.maximum data.offset data.sliceLen) ∧
      result.extra.locations.WellFormed ∧ result.extra.locations.size = data.allocation.extra.locations.size ∧
      S02SameDestinationAcceptedCopyPhysical.Physical result ∧
      ∃ activeThread, finalMachine.threads.activeThread? = some activeThread := by
  dsimp only
  obtain ⟨guardMachine,guardTrace,preserved,guardThread,guardActive⟩ :=
    from_copy options limits remaining span frames caller machine sourcePointer destinationPointer n input statementBudget statementFuel mode
  let root := CopyRootGuardEntry.rootFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input
  let after := returnedCopy options limits remaining span frames caller machine sourcePointer destinationPointer n input
  obtain ⟨body,identity,callee,location,size,returnPlace,continuation,varargs,noClocks,borrow⟩ :=
    returned_metadata options limits remaining span frames caller machine sourcePointer destinationPointer n input
  have rows := returned_locals options limits remaining span frames caller machine sourcePointer destinationPointer n input
  obtain ⟨v0,v1,v2,v3,v4,v5,v14,v15,v16,cell0,cell1,cell2,cell3,cell4,cell5,cell14,cell15,cell16⟩ :=
    returned_slots sourcePointer destinationPointer n after.locals rows
  have rootValid : (18 : MIR.LocalId) < root.locals.size := by
    simpa only [root,CopyRootGuardEntry.rootFrame,CopyRootEntry.cachedCaller,CopyUncachedCall.cachedCaller,
      LocalPlaces.cachePlaceLayout,Array.size_set] using input.valid
  have rootLive : (root.locals[18]'rootValid).value = .live (.immediate input.old) := by
    simpa only [root,CopyRootGuardEntry.rootFrame,CopyRootEntry.cachedCaller,CopyUncachedCall.cachedCaller,
      LocalPlaces.cachePlaceLayout,Array.getElem_set_self] using input.live
  have rootCached : (root.locals[18]'rootValid).layout = some CopyHelperUnit.layout := by
    simp only [root,CopyRootGuardEntry.rootFrame,CopyRootEntry.cachedCaller,CopyUncachedCall.cachedCaller,
      LocalPlaces.cachePlaceLayout,Array.getElem_set_self]
  have rootClocks : root.extra.dataRace = none := input.noClocks
  have destination : after.returnPlace.toRuntimePlace =
      LocalPlaces.localRuntimePlace frames.size root 18 CopyHelperUnit.layout := by rw [returnPlace];rfl
  obtain ⟨result,finalMachine,trace,lookup,bytes,len,tree,snapshot,memory,tracked,race,ghost,shallow,unchecked,noGc,fixed,
      addresses,types,backend,extras,physical,active⟩ := S02SameDestinationAcceptedCopyPhysicalRootComplete.of_guard_prefix
    options limits remaining span input.source input.debug input.fuel input.validationFuel frames root after guardMachine
    body identity callee location size input.tracker data.id data.tag data.base data.offset data.sliceLen n data.kind data.allocation
    data.positive data.sliceBounds data.copyBounds data.storage data.maskValid data.maskLen data.initialized data.valid data.storageFits data.mutable
    (preserved.race.trans input.noRace) (preserved.backend.trans input.backend) (preserved.tracker.trans input.tracked)
    (by rw [preserved.extras];exact data.extras) (by rw [preserved.memory];exact data.live)
    (by rw [preserved.addresses];exact data.cached) data.borrow data.bounded
    (by simp only [cell1]; exact congrArg (fun value => LocalValue.live (.immediate (.scalar value))) data.source) (by simp only [cell2]; exact congrArg (fun value => LocalValue.live (.immediate (.scalar value))) data.destination) (by rw [cell3])
    (by rw [cell1]) (by rw [cell2]) (by rw [cell3])
    (by rw [cell4]) (by rw [cell4]) (by rw [cell5]) (by rw [cell5])
    (by rw [cell14]) (by rw [cell14]) (by rw [cell15]) (by rw [cell15]) (by rw [cell16]) (by rw [cell16])
    (returned_all_immediate options limits remaining span frames caller machine sourcePointer destinationPointer n input)
    noClocks mode (preserved.unchecked.trans input.unchecked) (preserved.noGc.trans input.noGc)
    (preserved.fixed.trans input.fixed) (preserved.ghost.trans input.ghost) (preserved.validation.trans input.shallow)
    (by rw [cell0]) (by rw [cell0]) varargs ({} : FrameState) borrow rfl guardThread guardActive
    18 rootValid input.old rootLive rootCached rootClocks destination 9 .Continue continuation
    caller machine sourcePointer destinationPointer input guardTrace
  refine ⟨result,finalMachine,?_,lookup,bytes,len,tree,snapshot,?_,?_,race,ghost,shallow,unchecked,noGc,fixed,
    addresses.trans preserved.addresses,types.trans preserved.types,backend.trans preserved.backend,extras.trans preserved.extras,?_,?_,?_,?_,physical,active⟩
  · exact trace
  · exact memory.trans (congrArg (fun before => CopyHelperCall.memoryAfter before data.id data.kind result) preserved.memory)
  · simpa only [GlobalState.endCall,Array.foldl_empty] using tracked

  · rw [tree]
    exact (GeneralBorrowRawCopyInput.accesses data.allocation.extra input.tracker.global data.tag data.offset data.sliceLen n data.borrow).2.2.1
  · rw [tree]
    exact (GeneralBorrowRawCopyInput.accesses data.allocation.extra input.tracker.global data.tag data.offset data.sliceLen n data.borrow).2.2.2
  · rw [tree]
    exact (GeneralBorrowRawCopyInput.accesses data.allocation.extra input.tracker.global data.tag data.offset data.sliceLen n data.borrow).2.1.well
  · rw [tree]
    have accesses := GeneralBorrowRawCopyInput.accesses data.allocation.extra input.tracker.global data.tag data.offset data.sliceLen n data.borrow
    exact accesses.2.1.capacity.trans accesses.1.capacity

end DuplicatePrefix.S02SameDestinationAcceptedCopyPhysicalGuardBody
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.S02SameDestinationAcceptedCopyPhysicalGuardBody.complete) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved generic root actual copy dependency {dependency}"
