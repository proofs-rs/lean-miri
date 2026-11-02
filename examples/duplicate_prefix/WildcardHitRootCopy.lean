import duplicate_prefix.WildcardHitArgumentCopy
import duplicate_prefix.ConcreteEmptyRootCopy
namespace DuplicatePrefix.WildcardHitRootCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
abbrev changedFrame := ConcreteEmptyRootCopy.changedFrame

def changedMachine (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (global : GlobalState)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) :=
  {machine with
    borrowTracker := some ⟨TypedRetagGeneric.protectedGlobal global fresh,.FnEntry⟩
    memory := RetagEntry.updatedMemory machine.memory id entry
      (ActualWildcardHitReference.finalTree entry.allocation.extra global.nextPointerTag)}
theorem copy
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (global : GlobalState)
    (base : UInt64) (nonzero : base ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size) (old : Immediate Provenance)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some reference) (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some ⟨global,.FnEntry⟩)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (inverse : machine.user.addresses.intToPtrMap = #[⟨base,id⟩])
    (exposed : machine.user.addresses.exposed.contains id = true)
    (tagMapFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping global.nextPointerTag)
    (noFree : entry.allocation.extra.tagMapping.deassigned.back? = none)
    (fits : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false)
    (view : RuntimeStackPlace Provenance) (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size frame localId reference) :
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new .wildcard (Size.ofBytes base)) 0 reference).imm
    let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes base)) 0 reference).imm
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate value,reference⟩ view (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (changedFrame frame localId adjusted valid borrowFrame id global.nextPointerTag)
        (changedMachine machine global fresh id entry)) := by
  have result := WildcardHitArgumentCopy.copy options limits remaining span ctx debugOff cmp dynamicFuel validityFuel
    fuelEq validationEq id global base nonzero entry frames frame machine localId valid old live cached noClocks ghost shallow
    cachedAddress present borrowFrame frameBorrow enabled fresh addressMode inverse exposed tagMapFresh noFree fits
    metadata notConstructed view destination
  have restored : {machine.user with payload := {machine.user.payload with ghost := false}} = machine.user := by
    rw [←ghost]
  simpa only [changedFrame,ConcreteEmptyRootCopy.changedFrame,changedMachine,
    ActualWildcardHitReference.resultState,ReferenceBorrowDriver.allocatedMachine,
    ReferenceBorrowDriver.allocatedTracker,TypedBorrowSteps.registeredMachine,TypedBorrowSteps.registeredTracker,
    TypedBorrowSteps.registeredGlobal,TypedRetagGeneric.protectedGlobal,TypedRetagGeneric.allocatedGlobal,TypedBorrowSteps.registeredFrame,
    TypedRetagEntry.frameWithBorrow,ConcreteEmptyReferenceArgumentCopy.copiedFrame,Storage.withCurrent,
    Array.getElem_set_self,Array.set_set,restored] using result

end DuplicatePrefix.WildcardHitRootCopy
