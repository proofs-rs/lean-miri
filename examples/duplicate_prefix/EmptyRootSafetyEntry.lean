import duplicate_prefix.RawRootInvocation
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
namespace DuplicatePrefix.EmptyRootSafetyEntry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Interpreter
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver
theorem enters
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualRetagContext.Context options (remaining+1) span)
    (place : MPlaceTy Provenance) (layout : place.layout = RootCompilerFacts.boolLayout)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tracker : MachineHooks.BorrowState)
    (enabled : before.borrowTracker = some tracker)
    (initialFresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (fresh : (TypedRetagEmpty.successorTag tracker.global.nextPointerTag initialFresh).value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base : UInt64) (rootTag : BorTag)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id rootTag)) (Size.ofBytes base))
    (aligned : place.mplace.misaligned = none)
    (cached : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (root : entry.allocation.extra = BorrowTree.new rootTag (Size.ofBytes 1))
    (size : entry.allocation.byteSize = Size.ofBytes 1)
    (present : before.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (race : before.dataRace = none)
    (distinct : rootTag ≠ TypedRetagEmpty.successorTag tracker.global.nextPointerTag initialFresh)
    (unprotected : tracker.global.protectedTags.contains rootTag = false)
    (mutable : entry.allocation.mutability = .Mut)
    (storage : entry.allocation.len = entry.allocation.byteSize.bytes.toNat)
    (maskLength : entry.allocation.initializationMask.len = entry.allocation.byteSize)
    (provenance : entry.allocation.provenanceMap = ProvenanceMap.new)
    (noBackend : before.user.payload.payload.user.backend = .none)
    (extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩))
    (ghost : before.user.payload.ghost = false)
    (address count : UInt64) (nonzero : address ≠ 0)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (precise : options.retag.preciseInteriorMut = false) (implicitWrites : options.retag.implicitWrites = false)
    (debug : options.place.debugAssertions = false) (dynamicFuel validityFuel : Nat)
    (dynamicEq : options.place.dynamicFuel = dynamicFuel+1) (validityEq : options.limits.validation = validityFuel+1)
    (shallow : before.user.payload.validation = .Shallow)
    (metadata : before.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : before.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (thread : Miri.Concurrency.ThreadRecord)
    (active : before.threads.activeThread? = some thread)
    (noCache : thread.topUserRelevantFrame = none)
 :
    let argsFrame := EmptyRootArguments.result (RawRootInvocation.root before place race) address count
    let argsMachine := allocatedMachine (RawRootInvocation.machine #[] before) tracker initialFresh
    let next := allocatedTracker tracker initialFresh
    let changed := {argsFrame.frame with location := FrameLocation.unwinding ⟨601⟩}
    let borrowed := ReturnProtection.borrowedState #[] changed {} argsMachine next fresh id entry
      (PhysicalMachineWrite.slotTree rootTag next.global.nextPointerTag 1 false)
    ∃ updated,
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (EmptyRootArguments.first address), .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true) ⟨⟨#[]⟩,before⟩ =
      .ok () (Storage.withCurrent #[]
        (CallEntryFacts.doneRootFrame {registeredFrame changed {} id next.global.nextPointerTag with location := .unwinding ⟨559⟩})
        (CanonicalCopy.replaceAllocation borrowed id entry.kind updated).machine) ∧
      updated.extra = PhysicalMachineWrite.slotTree rootTag next.global.nextPointerTag 1 true ∧
      updated.byteSize = Size.ofBytes 1 ∧ updated.len = 1 ∧
      updated.initializationMask = InitMask.new (Size.ofBytes 1) false ∧
      updated.provenanceMap = ProvenanceMap.new ∧ AllocationCopy.snapshot updated = AllocationCopy.snapshot entry.allocation ∧
      updated.mutability = .Mut := by
  let raw := RawRootInvocation.root before place race
  let machine := RawRootInvocation.machine #[] before
  obtain ⟨memory,borrow,dataRace,addresses,ghostEq,validation,types,backend,extraEq⟩ := RawRootInvocation.preservation #[] before
  have slot (i : Fin 25) : (raw.frame.locals[i.val]'(raw.valid i)) = ⟨.dead,none⟩ := by
    have rows := congrArg (fun rows : Array (LocalState Provenance LocalLayout) => rows[i.val]?)
      (RawRootInvocation.locals before place race)
    have row : raw.frame.locals[i.val]?=some (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
      simpa only [Array.getElem?_replicate, i.isLt, ↓reduceIte] using rows
    exact Option.some.inj ((Array.getElem?_eq_getElem (raw.valid i)).symm.trans row)
  have frameBorrow := RawRootInvocation.frame_borrow before place race tracker enabled
  have control := RawRootInvocation.control before place race
  have enabledRaw : machine.borrowTracker=some tracker := borrow.trans enabled
  have cachedRaw : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id)=some ⟨id,base⟩ := by rw [addresses];exact cached
  have presentRaw : machine.memory.live.find? (fun row => row.1 == id)=some (id,entry) := by rw [memory];exact present
  have raceRaw : machine.dataRace=none := dataRace.trans race
  have backendRaw : machine.user.payload.payload.user.backend=.none := backend.trans noBackend
  have extrasRaw : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id)=some (id,⟨none,#[]⟩) := by
    rw [extraEq];exact extras
  have ghostRaw : machine.user.payload.ghost=false := ghostEq.trans ghost
  have shallowRaw : machine.user.payload.validation=.Shallow := validation.trans shallow
  have metadataRaw : machine.user.payload.payload.user.types.metadata=PreparedReflection.actual.runtime := by rw [types];exact metadata
  have notConstructedRaw : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4)=false := by rw [types];exact notConstructed
  exact EmptyRootCallEntry.actual_entry options limits remaining span ctx place layout #[] raw {} machine tracker enabledRaw frameBorrow
    initialFresh fresh id entry base rootTag pointer aligned cachedRaw root size presentRaw raceRaw distinct unprotected mutable storage maskLength
    provenance backendRaw extrasRaw ghostRaw (by rw [slot ⟨0,by decide⟩]) (by rw [slot ⟨6,by decide⟩])
    (by rw [slot ⟨13,by decide⟩]) (by rw [slot ⟨14,by decide⟩]) address count nonzero cmp precise implicitWrites debug dynamicFuel validityFuel
    dynamicEq validityEq shallowRaw metadataRaw notConstructedRaw (congrArg (fun row => row.value) (slot EmptyRootArguments.i1)) (congrArg (fun row => row.layout) (slot EmptyRootArguments.i1))
    (congrArg (fun row => row.value) (slot EmptyRootArguments.i2)) (congrArg (fun row => row.layout) (slot EmptyRootArguments.i2)) ⟨⟨#[]⟩,before⟩ thread active noCache
    (RawRootInvocation.raw_eq #[] before place race) control.1 control.2.1

#print axioms enters
end DuplicatePrefix.EmptyRootSafetyEntry
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.EmptyRootSafetyEntry.enters) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved genuine root zero entry dependency {dependency}"
