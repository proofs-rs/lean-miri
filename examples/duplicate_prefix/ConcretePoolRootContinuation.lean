import duplicate_prefix.ConcreteEmptyRootArgumentProperties
import duplicate_prefix.ConcretePoolRootArgumentScope
import duplicate_prefix.RootEntryTail
import duplicate_prefix.ProtectorInsertion
import duplicate_prefix.StackPopRelease
namespace DuplicatePrefix.ConcretePoolRootContinuation
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts RootFrameData EmptyRootArguments ActualReferenceContext ConcreteEmptyRootArguments ConcretePoolRootArgumentScope
open TypedBorrowSteps ReferenceBorrowDriver
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable def continuation (h : RootCallCore.RootHooks) (first : OpTy Provenance) (n : UInt64) (place : MPlaceTy Provenance) :
    MachineHooks.M MiriMemoryKind Machine.RootUser Unit := do
  let _ ← h.withRetagMode () .FnEntry (RootCallCore.argumentBody h first (second n))
  RootEntryTail.tail h place
theorem succeeds
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (parentTag : BorTag) (tracker : MachineHooks.BorrowState)
    (base offset n : UInt64) (nonzero : base+offset ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (frames : Array CompilerFrameContext.ActualFrame) (root : RootFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (dead1 : (root.frame.locals[1]'(root.valid i1)).value = .dead)
    (cache1 : (root.frame.locals[1]'(root.valid i1)).layout = none)
    (dead2 : (root.frame.locals[2]'(root.valid i2)).value = .dead)
    (cache2 : (root.frame.locals[2]'(root.valid i2)).layout = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (borrowFrame : FrameState) (frameBorrow : root.frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (entryInput : ConcreteEmptyPoolEntry.Input entry.allocation.extra parentTag tracker.global.nextPointerTag)
    (race : machine.dataRace = none)
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (retagCtx : ActualRetagContext.Context options (remaining+1) span)
    (place : MPlaceTy Provenance) (layout : place.layout = RootCompilerFacts.boolLayout)
    (slotId : AllocId) (slotEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (slotBase : UInt64) (slotRoot : BorTag)
    (slotPointer : place.mplace.ptr = Pointer.new (some (.concrete slotId slotRoot)) (Size.ofBytes slotBase))
    (aligned : place.mplace.misaligned = none)
    (slotCached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == slotId) = some ⟨slotId,slotBase⟩)
    (slotTree : slotEntry.allocation.extra = BorrowTree.new slotRoot (Size.ofBytes 1))
    (slotSize : slotEntry.allocation.byteSize = Size.ofBytes 1)
    (slotPresent : machine.memory.live.find? (fun row => row.1 == slotId) = some (slotId,slotEntry))
    (separate : slotId ≠ id)
    (slotFresh : (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value < 18446744073709551615)
    (slotDistinct : slotRoot ≠ TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh)
    (slotParentDistinct : slotRoot ≠ tracker.global.nextPointerTag)
    (slotFree : tracker.global.protectedTags.contains slotRoot = false)
    (mutable : slotEntry.allocation.mutability = .Mut)
    (storage : slotEntry.allocation.len = slotEntry.allocation.byteSize.bytes.toNat)
    (maskLength : slotEntry.allocation.initializationMask.len = slotEntry.allocation.byteSize)
    (provenance : slotEntry.allocation.provenanceMap = ProvenanceMap.new)
    (noBackend : machine.user.payload.payload.user.backend = .none)
    (extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == slotId) = some (slotId,⟨none,#[]⟩))
    (dead0 : (root.frame.locals[0]'(root.valid ⟨0,by decide⟩)).value = .dead)
    (dead6 : (root.frame.locals[6]'(root.valid ⟨6,by decide⟩)).value = .dead)
    (dead13 : (root.frame.locals[13]'(root.valid ⟨13,by decide⟩)).value = .dead)
    (dead14 : (root.frame.locals[14]'(root.valid ⟨14,by decide⟩)).value = .dead) :
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
    let argsFrame := RootArgumentsTwo.result (ConcreteEmptyRootArguments.firstDone root adjusted borrowFrame id tracker.global.nextPointerTag) n
    let argsMachine := resultMachine machine tracker fresh id entry parentTag entryInput
    let next : MachineHooks.BorrowState := ⟨TypedRetagGeneric.protectedGlobal tracker.global fresh,tracker.retagMode⟩
    let owned := borrowFrame.addProtector id tracker.global.nextPointerTag
    let changed := {argsFrame.frame with location := FrameLocation.unwinding ⟨601⟩}
    let borrowed := ReturnProtection.borrowedState frames changed owned argsMachine next slotFresh slotId slotEntry
      (PhysicalMachineWrite.slotTree slotRoot next.global.nextPointerTag 1 false)
    ∃ updated,
      continuation (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
        ⟨.immediate value,ActualReferenceMetadata.reference⟩ n place (Storage.withCurrent frames root.frame machine) =
      .ok () (Storage.withCurrent frames
        (CallEntryFacts.doneRootFrame {registeredFrame changed owned slotId next.global.nextPointerTag with location := .unwinding ⟨559⟩})
        (CanonicalCopy.replaceAllocation borrowed slotId slotEntry.kind updated).machine) ∧
      updated.extra = PhysicalMachineWrite.slotTree slotRoot next.global.nextPointerTag 1 true ∧
      updated.byteSize = Size.ofBytes 1 ∧ updated.len = 1 ∧
      updated.initializationMask = InitMask.new (Size.ofBytes 1) false ∧
      updated.provenanceMap = ProvenanceMap.new ∧ AllocationCopy.snapshot updated = AllocationCopy.snapshot slotEntry.allocation ∧
      updated.mutability = .Mut := by
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
  let argsFrame := RootArgumentsTwo.result (ConcreteEmptyRootArguments.firstDone root adjusted borrowFrame id tracker.global.nextPointerTag) n
  let argsMachine := resultMachine machine tracker fresh id entry parentTag entryInput
  let next : MachineHooks.BorrowState := ⟨TypedRetagGeneric.protectedGlobal tracker.global fresh,tracker.retagMode⟩
  let owned := borrowFrame.addProtector id tracker.global.nextPointerTag
  let changed := {argsFrame.frame with location := FrameLocation.unwinding ⟨601⟩}
  let borrowed := ReturnProtection.borrowedState frames changed owned argsMachine next slotFresh slotId slotEntry
      (PhysicalMachineWrite.slotTree slotRoot next.global.nextPointerTag 1 false)
  have arguments := ConcretePoolRootArgumentScope.scope options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id parentTag tracker base offset n nonzero entry frames root machine
    dead1 cache1 dead2 cache2 ghost shallow cachedAddress present borrowFrame frameBorrow enabled fresh entryInput metadata notConstructed
  have presentAfter : argsMachine.memory.live.find? (fun row => row.1 == slotId) = some (slotId,slotEntry) :=
    StackPopRelease.lookup_commit_other machine.memory id slotId entry slotEntry
      entryInput.after separate slotPresent
  have freeAfter : next.global.protectedTags.contains slotRoot = false := by
    change (tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector).contains slotRoot = false
    rw [ProtectorInsertion.contains_other tracker.global.protectedTags tracker.global.nextPointerTag slotRoot .StrongProtector slotParentDistinct]
    exact slotFree
  have d0 : (argsFrame.frame.locals[0]'(argsFrame.valid ⟨0,by decide⟩)).value = .dead := by
    rw [ConcreteEmptyRootArgumentProperties.untouched root adjusted borrowFrame id tracker.global.nextPointerTag n ⟨0,by decide⟩ (by decide) (by decide)];exact dead0
  have d6 : (argsFrame.frame.locals[6]'(argsFrame.valid ⟨6,by decide⟩)).value = .dead := by
    rw [ConcreteEmptyRootArgumentProperties.untouched root adjusted borrowFrame id tracker.global.nextPointerTag n ⟨6,by decide⟩ (by decide) (by decide)];exact dead6
  have d13 : (argsFrame.frame.locals[13]'(argsFrame.valid ⟨13,by decide⟩)).value = .dead := by
    rw [ConcreteEmptyRootArgumentProperties.untouched root adjusted borrowFrame id tracker.global.nextPointerTag n ⟨13,by decide⟩ (by decide) (by decide)];exact dead13
  have d14 : (argsFrame.frame.locals[14]'(argsFrame.valid ⟨14,by decide⟩)).value = .dead := by
    rw [ConcreteEmptyRootArgumentProperties.untouched root adjusted borrowFrame id tracker.global.nextPointerTag n ⟨14,by decide⟩ (by decide) (by decide)];exact dead14
  obtain ⟨updated,tail,props⟩ := RootEntryTail.actual_tail options limits (remaining+1) span retagCtx place layout
    frames argsFrame.frame owned argsMachine next rfl rfl slotFresh slotId slotEntry slotBase slotRoot slotPointer aligned slotCached slotTree slotSize
    presentAfter race slotDistinct freeAfter mutable storage maskLength provenance noBackend extras ghost argsFrame.body argsFrame.size
    d0 d6 d13 d14 argsFrame.noClocks argsFrame.identity argsFrame.callee
  refine ⟨updated,?_,props⟩
  unfold continuation
  simp only [bind,EStateM.bind]
  rw [arguments]
  exact tail
end
end DuplicatePrefix.ConcretePoolRootContinuation
