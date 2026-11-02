import duplicate_prefix.ConcreteEmptyRootCallEntry
import duplicate_prefix.RawRootInvocation
namespace DuplicatePrefix.ConcreteEmptyRootInvocationEntry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts RootFrameData EmptyRootArguments ActualReferenceContext ConcreteEmptyRootArguments ConcreteEmptyRootArgumentScope
open TypedBorrowSteps ReferenceBorrowDriver
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem enters
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (parentTag : BorTag) (tracker : MachineHooks.BorrowState)
    (base offset capacity n : UInt64) (nonzero : base+offset ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (ghost : before.user.payload.ghost = false) (shallow : before.user.payload.validation = .Shallow)
    (cachedAddress : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : before.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (enabled : before.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (distinct : parentTag ≠ tracker.global.nextPointerTag) (rootUnprotected : tracker.global.protectedTags.contains parentTag = false)
    (tree : entry.allocation.extra = BorrowTree.new parentTag (Size.ofBytes capacity))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity) (race : before.dataRace = none)
    (metadata : before.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : before.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (retagCtx : ActualRetagContext.Context options (remaining+1) span)
    (place : MPlaceTy Provenance) (layout : place.layout = RootCompilerFacts.boolLayout)
    (slotId : AllocId) (slotEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (slotBase : UInt64) (slotRoot : BorTag)
    (slotPointer : place.mplace.ptr = Pointer.new (some (.concrete slotId slotRoot)) (Size.ofBytes slotBase))
    (aligned : place.mplace.misaligned = none)
    (slotCached : before.user.addresses.baseAddr.find? (fun row => row.allocId == slotId) = some ⟨slotId,slotBase⟩)
    (slotTree : slotEntry.allocation.extra = BorrowTree.new slotRoot (Size.ofBytes 1))
    (slotSize : slotEntry.allocation.byteSize = Size.ofBytes 1)
    (slotPresent : before.memory.live.find? (fun row => row.1 == slotId) = some (slotId,slotEntry))
    (separate : slotId ≠ id)
    (slotFresh : (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value < 18446744073709551615)
    (slotDistinct : slotRoot ≠ TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh)
    (slotParentDistinct : slotRoot ≠ tracker.global.nextPointerTag)
    (slotFree : tracker.global.protectedTags.contains slotRoot = false)
    (mutable : slotEntry.allocation.mutability = .Mut)
    (storage : slotEntry.allocation.len = slotEntry.allocation.byteSize.bytes.toNat)
    (maskLength : slotEntry.allocation.initializationMask.len = slotEntry.allocation.byteSize)
    (provenance : slotEntry.allocation.provenanceMap = ProvenanceMap.new)
    (noBackend : before.user.payload.payload.user.backend = .none)
    (extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == slotId) = some (slotId,⟨none,#[]⟩))
    (thread : Miri.Concurrency.ThreadRecord)
    (active : before.threads.activeThread? = some thread)
    (noCache : thread.topUserRelevantFrame = none) :
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
    let argsFrame := RootArgumentsTwo.result (firstDone (RawRootInvocation.root before place race) adjusted ({} : FrameState) id tracker.global.nextPointerTag) n
    let argsMachine := resultMachine (RawRootInvocation.machine #[] before) tracker fresh id entry parentTag capacity
    let next : MachineHooks.BorrowState := ⟨TypedRetagGeneric.protectedGlobal tracker.global fresh,tracker.retagMode⟩
    let owned := ({} : FrameState).addProtector id tracker.global.nextPointerTag
    let changed := {argsFrame.frame with location := FrameLocation.unwinding ⟨601⟩}
    let borrowed := ReturnProtection.borrowedState #[] changed owned argsMachine next slotFresh slotId slotEntry
      (PhysicalMachineWrite.slotTree slotRoot next.global.nextPointerTag 1 false)
    ∃ updated,
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩,.Copy (second n)] false (.memory place) (.stop true) ⟨⟨#[]⟩,before⟩ =
      .ok () (Storage.withCurrent #[]
        (CallEntryFacts.doneRootFrame {registeredFrame changed owned slotId next.global.nextPointerTag with location := .unwinding ⟨559⟩})
        (CanonicalCopy.replaceAllocation borrowed slotId slotEntry.kind updated).machine) ∧
      updated.extra = PhysicalMachineWrite.slotTree slotRoot next.global.nextPointerTag 1 true ∧
      updated.byteSize = Size.ofBytes 1 ∧ updated.len = 1 ∧
      updated.initializationMask = InitMask.new (Size.ofBytes 1) false ∧
      updated.provenanceMap = ProvenanceMap.new ∧ AllocationCopy.snapshot updated = AllocationCopy.snapshot slotEntry.allocation ∧
      updated.mutability = .Mut := by
  let raw := RawRootInvocation.root before place race
  let machine := RawRootInvocation.machine #[] before
  obtain ⟨memory,borrow,dataRace,addresses,ghostEq,validation,types,backend,extraEq⟩ := RawRootInvocation.preservation #[] before
  have slot (i : Fin 25) : (raw.frame.locals[i.val]'(raw.valid i)) = ⟨.dead,none⟩ := by
    have rows := congrArg (fun rows : Array (LocalState Provenance LocalLayout) => rows[i.val]?)
      (RawRootInvocation.locals before place race)
    have row : raw.frame.locals[i.val]?=some (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
      simpa only [Array.getElem?_replicate,i.isLt,↓reduceIte] using rows
    exact Option.some.inj ((Array.getElem?_eq_getElem (raw.valid i)).symm.trans row)
  have frameBorrow := RawRootInvocation.frame_borrow before place race tracker enabled
  have control := RawRootInvocation.control before place race
  have enabledRaw : machine.borrowTracker = some tracker := borrow.trans enabled
  have cachedRaw : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by rw [addresses];exact cachedAddress
  have presentRaw : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry) := by rw [memory];exact present
  have slotCachedRaw : machine.user.addresses.baseAddr.find? (fun row => row.allocId == slotId) = some ⟨slotId,slotBase⟩ := by rw [addresses];exact slotCached
  have slotPresentRaw : machine.memory.live.find? (fun row => row.1 == slotId) = some (slotId,slotEntry) := by rw [memory];exact slotPresent
  have raceRaw : machine.dataRace = none := dataRace.trans race
  have backendRaw : machine.user.payload.payload.user.backend = .none := backend.trans noBackend
  have extrasRaw : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == slotId) = some (slotId,⟨none,#[]⟩) := by rw [extraEq];exact extras
  have ghostRaw : machine.user.payload.ghost = false := ghostEq.trans ghost
  have shallowRaw : machine.user.payload.validation = .Shallow := validation.trans shallow
  have metadataRaw : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime := by rw [types];exact metadata
  have notConstructedRaw : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false := by rw [types];exact notConstructed
  exact ConcreteEmptyRootCallEntry.actual_entry options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id parentTag tracker base offset capacity n nonzero entry #[] raw machine
    (congrArg (fun row => row.value) (slot i1)) (congrArg (fun row => row.layout) (slot i1))
    (congrArg (fun row => row.value) (slot i2)) (congrArg (fun row => row.layout) (slot i2)) ghostRaw shallowRaw
    cachedRaw presentRaw {} frameBorrow enabledRaw fresh distinct rootUnprotected tree allocationSize raceRaw metadataRaw notConstructedRaw
    retagCtx place layout slotId slotEntry slotBase slotRoot slotPointer aligned slotCachedRaw slotTree slotSize slotPresentRaw separate slotFresh slotDistinct
    slotParentDistinct slotFree mutable storage maskLength provenance backendRaw extrasRaw
    (by rw [slot ⟨0,by decide⟩]) (by rw [slot ⟨6,by decide⟩]) (by rw [slot ⟨13,by decide⟩]) (by rw [slot ⟨14,by decide⟩])
    ⟨⟨#[]⟩,before⟩ thread active noCache (RawRootInvocation.raw_eq #[] before place race) control.1 control.2.1
end
end DuplicatePrefix.ConcreteEmptyRootInvocationEntry

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.ConcreteEmptyRootInvocationEntry.enters) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved genuine positive root entry dependency {dependency}"
