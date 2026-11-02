import duplicate_prefix.RootEntryTail
import duplicate_prefix.WildcardEmptyRootArgumentScope
import duplicate_prefix.WildcardEmptyRootArgumentProperties
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
namespace DuplicatePrefix.WildcardEmptyRootContinuation
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Interpreter
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver
noncomputable def continuation (h : RootCallCore.RootHooks) (target : TargetDataLayout) (address n : UInt64) (place : MPlaceTy Provenance) : MachineHooks.M MiriMemoryKind Machine.RootUser Unit := do
  let _ ← h.withRetagMode () .FnEntry (RootCallCore.argumentBody h (WildcardEmptyRootArguments.first target address) (WildcardEmptyRootArguments.second n))
  RootEntryTail.tail h place
theorem succeeds
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualRetagContext.Context options (remaining+1) span)
    (place : MPlaceTy Provenance) (layout : place.layout = RootCompilerFacts.boolLayout)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (rootFrame : RootFrameData.RootFrame) (borrowFrame : FrameState)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (frameBorrow : rootFrame.frame.extra.borrowTracker = some borrowFrame)
    (initialFresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (fresh : (TypedRetagEmpty.successorTag tracker.global.nextPointerTag initialFresh).value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base : UInt64) (rootTag : BorTag)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id rootTag)) (Size.ofBytes base))
    (aligned : place.mplace.misaligned = none)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (root : entry.allocation.extra = BorrowTree.new rootTag (Size.ofBytes 1))
    (size : entry.allocation.byteSize = Size.ofBytes 1)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (race : machine.dataRace = none)
    (distinct : rootTag ≠ TypedRetagEmpty.successorTag tracker.global.nextPointerTag initialFresh)
    (unprotected : tracker.global.protectedTags.contains rootTag = false)
    (mutable : entry.allocation.mutability = .Mut)
    (storage : entry.allocation.len = entry.allocation.byteSize.bytes.toNat)
    (maskLength : entry.allocation.initializationMask.len = entry.allocation.byteSize)
    (provenance : entry.allocation.provenanceMap = ProvenanceMap.new)
    (noBackend : machine.user.payload.payload.user.backend = .none)
    (extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩))
    (ghost : machine.user.payload.ghost = false)
    (dead0 : (rootFrame.frame.locals[0]'(rootFrame.valid ⟨0,by decide⟩)).value = .dead)
    (dead6 : (rootFrame.frame.locals[6]'(rootFrame.valid ⟨6,by decide⟩)).value = .dead)
    (dead13 : (rootFrame.frame.locals[13]'(rootFrame.valid ⟨13,by decide⟩)).value = .dead)
    (dead14 : (rootFrame.frame.locals[14]'(rootFrame.valid ⟨14,by decide⟩)).value = .dead)
    (target : TargetDataLayout)
    (targetEq : target = (ActualReferenceContext.config options remaining span).access.runtime.base)
    (address n : UInt64) (nonzero : address ≠ 0)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (precise : options.retag.preciseInteriorMut = false) (implicitWrites : options.retag.implicitWrites = false)
    (debug : options.place.debugAssertions = false) (dynamicFuel validityFuel : Nat)
    (dynamicEq : options.place.dynamicFuel = dynamicFuel+1) (validityEq : options.limits.validation = validityFuel+1)
    (shallow : machine.user.payload.validation = .Shallow)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (below : ∀ entry ∈ machine.user.addresses.intToPtrMap, address < entry.address)
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (dead1 : (rootFrame.frame.locals[1]'(rootFrame.valid WildcardEmptyRootArguments.i1)).value = .dead)
    (cache1 : (rootFrame.frame.locals[1]'(rootFrame.valid WildcardEmptyRootArguments.i1)).layout = none)
    (dead2 : (rootFrame.frame.locals[2]'(rootFrame.valid WildcardEmptyRootArguments.i2)).value = .dead)
    (cache2 : (rootFrame.frame.locals[2]'(rootFrame.valid WildcardEmptyRootArguments.i2)).layout = none) :
    let argsFrame := WildcardEmptyRootArguments.result rootFrame target address n
    let argsMachine := allocatedMachine machine tracker initialFresh
    let next := allocatedTracker tracker initialFresh
    let changed := {argsFrame.frame with location := FrameLocation.unwinding ⟨601⟩}
    let borrowed := ReturnProtection.borrowedState frames changed borrowFrame argsMachine next fresh id entry
      (PhysicalMachineWrite.slotTree rootTag next.global.nextPointerTag 1 false)
    ∃ updated,
      continuation (ExecutionMachine.callHooks (config options (remaining+1) span) limits) target address n place
        (Storage.withCurrent frames rootFrame.frame machine) =
      .ok () (Storage.withCurrent frames
        (CallEntryFacts.doneRootFrame {registeredFrame changed borrowFrame id next.global.nextPointerTag with location := .unwinding ⟨559⟩})
        (CanonicalCopy.replaceAllocation borrowed id entry.kind updated).machine) ∧
      updated.extra = PhysicalMachineWrite.slotTree rootTag next.global.nextPointerTag 1 true ∧
      updated.byteSize = Size.ofBytes 1 ∧ updated.len = 1 ∧
      updated.initializationMask = InitMask.new (Size.ofBytes 1) false ∧
      updated.provenanceMap = ProvenanceMap.new ∧ AllocationCopy.snapshot updated = AllocationCopy.snapshot entry.allocation ∧
      updated.mutability = .Mut := by
  let argsFrame := WildcardEmptyRootArguments.result rootFrame target address n
  let argsMachine := allocatedMachine machine tracker initialFresh
  let next := allocatedTracker tracker initialFresh
  have arguments := WildcardEmptyRootArgumentScope.arguments_in_scope options limits remaining span cmp precise implicitWrites debug
    dynamicFuel validityFuel dynamicEq validityEq frames rootFrame machine target targetEq address n nonzero dead1 cache1 dead2 cache2
    ghost shallow tracker enabled initialFresh addressMode below metadata notConstructed
  have d0 : (argsFrame.frame.locals[0]'(argsFrame.valid ⟨0,by decide⟩)).value = .dead := by
    rw [WildcardEmptyRootArgumentProperties.untouched rootFrame target address n ⟨0,by decide⟩ (by decide) (by decide)]; exact dead0
  have d6 : (argsFrame.frame.locals[6]'(argsFrame.valid ⟨6,by decide⟩)).value = .dead := by
    rw [WildcardEmptyRootArgumentProperties.untouched rootFrame target address n ⟨6,by decide⟩ (by decide) (by decide)]; exact dead6
  have d13 : (argsFrame.frame.locals[13]'(argsFrame.valid ⟨13,by decide⟩)).value = .dead := by
    rw [WildcardEmptyRootArgumentProperties.untouched rootFrame target address n ⟨13,by decide⟩ (by decide) (by decide)]; exact dead13
  have d14 : (argsFrame.frame.locals[14]'(argsFrame.valid ⟨14,by decide⟩)).value = .dead := by
    rw [WildcardEmptyRootArgumentProperties.untouched rootFrame target address n ⟨14,by decide⟩ (by decide) (by decide)]; exact dead14
  obtain ⟨updated, tail, props⟩ := RootEntryTail.actual_tail options limits (remaining+1) span ctx place layout
    frames argsFrame.frame borrowFrame argsMachine next rfl frameBorrow fresh id entry base rootTag pointer aligned cached root size present
    race distinct unprotected mutable storage maskLength provenance noBackend extras ghost argsFrame.body argsFrame.size d0 d6 d13 d14 argsFrame.noClocks argsFrame.identity argsFrame.callee
  let changed := {argsFrame.frame with location := FrameLocation.unwinding ⟨601⟩}
  let borrowed := ReturnProtection.borrowedState frames changed borrowFrame argsMachine next fresh id entry
    (PhysicalMachineWrite.slotTree rootTag next.global.nextPointerTag 1 false)
  let final := Storage.withCurrent frames
    (CallEntryFacts.doneRootFrame {registeredFrame changed borrowFrame id next.global.nextPointerTag with location := .unwinding ⟨559⟩})
    (CanonicalCopy.replaceAllocation borrowed id entry.kind updated).machine
  refine ⟨updated, ?_, props⟩
  unfold continuation
  simp only [bind, EStateM.bind]
  rw [arguments]
  simp only [EStateM.bind]
  exact tail
end DuplicatePrefix.WildcardEmptyRootContinuation
