import duplicate_prefix.WildcardStaticEmptyReferenceCopy
import duplicate_prefix.ConcreteEmptyRootCopy
import duplicate_prefix.WildcardPoolHitRootCopy

namespace DuplicatePrefix.WildcardStaticEmptyRootCopy
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

def preparedMachine (options : EvalConfigurationCore.Options)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit) (converted : Allocation Provenance Unit) :=
  GlobalDataOnlyMaterialize.cached (GlobalDataOnlyActualConfig.extras options) machine id .global
    (converted.mapExtra (fun _ => BorrowTree.new root source.byteSize))

def entry (root : BorTag) (source : Allocation CtfeProvenance Unit) (converted : Allocation Provenance Unit) :
    LocalAllocation Provenance BorrowTree MiriMemoryKind :=
  ⟨.machine .global,converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)⟩

theorem post_machine (options : EvalConfigurationCore.Options)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (global : GlobalState) (fresh : global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit) (converted : Allocation Provenance Unit)
    (ghost : machine.user.payload.ghost = false) :
    let active := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
    let after := (WildcardStaticEmptyReferencePointer.resultState options frames frame borrowFrame active
      ⟨global,.FnEntry⟩ fresh id root source converted).machine
    {after with user := {after.user with payload := {after.user.payload with ghost := false}}} =
      WildcardPoolHitRootCopy.changedMachine (preparedMachine options machine id root source converted) global fresh
        id (entry root source converted) (WildcardStaticEmptyReferenceReborrow.rootSlot root source.byteSize) := by
  have restore : {machine.user with payload := {machine.user.payload with ghost := false}} = machine.user := by
    rw [←ghost]
  simp only [WildcardStaticEmptyReferencePointer.resultState,WildcardStaticEmptyReferenceReborrow.completed,
    WildcardStaticEmptyReferenceReborrow.materialized,GlobalDataOnlyMaterialize.cached,
    TypedBorrowSteps.registeredState,TypedBorrowSteps.registeredMachine,TypedBorrowSteps.registeredTracker,
    TypedBorrowSteps.registeredGlobal,ReferenceBorrowDriver.allocatedMachine,ReferenceBorrowDriver.allocatedTracker,
    WildcardPoolHitRootCopy.changedMachine,preparedMachine,entry,
    TypedRetagGeneric.protectedGlobal,TypedRetagGeneric.allocatedGlobal,Storage.withCurrent,
    MemoryExtras.putAllocation,GlobalDataOnlyActualConfig.extras,EvalCoreMachine.extras,
    WildcardStaticEmptyReferenceReborrow.finalTree,ActualWildcardPoolHitReference.finalTree]
  simp only [←ghost]
theorem copy (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (actualPointers : ctx.pointers = GlobalDataOnlyActualConfig.pointers PreparedReflection.actual.compiler
      PreparedReflection.actual.image (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions) ())
    (limits : ExecutionMachine.Limits)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel + 1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (parentTag : BorTag) (global : GlobalState)
    (base offset : UInt64) (nonzero : base + offset ≠ 0)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (valid : localId < frame.locals.size)
    (old : Immediate Provenance)
    (live : frame.locals[localId].value = .live (.immediate old))
    (noClocks : frame.extra.dataRace = none)
    (cached : frame.locals[localId].layout = some reference)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some ⟨global, .FnEntry⟩)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (distinct : parentTag ≠ global.nextPointerTag)
    (source : Allocation CtfeProvenance Unit) (definition : Nat)
    (initializer : PreparedReflection.actual.image.initializers.find? (·.1 == definition) = some (definition,source)) (supported : GlobalSupportedImage.Supported source PreparedReflection.actual.compiler.runtime.target
      machine.memory global.rootPointerTags machine.user.addresses.baseAddr)
    (rootCached : global.rootTag? id = some parentTag)
    (race : machine.dataRace = none)
    (noExtras : (machine.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id)) = false)
    (absent : machine.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : machine.memory.hasFunctionPointer id = false)
    (noVaList : machine.memory.hasVaListId id = false)
    (descriptor : machine.memory.findGlobal? id = some
      ⟨id,.static,source.byteSize,source.align,source.mutability,some (.static definition true false false)⟩)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (geometry : WildcardGeneralHitReborrow.Geometry machine.user.addresses.intToPtrMap (base+offset) base id source.byteSize)
    (exposed : machine.user.addresses.exposed.contains id = true)
    (allocLive : machine.memory.isAllocLive id = true)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any
      (·.value.ty == 4) = false)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size frame localId reference)
    : ∃ converted : Allocation Provenance Unit,
      GlobalAllocationAttributes.Attributes source converted ∧
      let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base+offset))) 0 reference).imm
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
        ⟨.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new .wildcard (Size.ofBytes (base+offset))) 0 reference).imm,reference⟩
        view (Storage.withCurrent frames frame machine) =
        .ok () (Storage.withCurrent frames
          (ConcreteEmptyRootCopy.changedFrame frame localId adjusted valid borrowFrame id global.nextPointerTag)
          (WildcardPoolHitRootCopy.changedMachine (preparedMachine options machine id parentTag source converted)
            global fresh id (entry parentTag source converted) (WildcardStaticEmptyReferenceReborrow.rootSlot parentTag source.byteSize))) := by
  obtain ⟨converted,facts,result⟩ := WildcardStaticEmptyReferenceCopy.copy_argument options remaining span ctx actualPointers
    limits debugOff cmp dynamicFuel validityFuel fuelEq validationEq id parentTag global base offset nonzero
    frames frame machine localId valid old live noClocks cached ghost shallow cachedAddress borrowFrame frameBorrow
    enabled fresh distinct source definition initializer supported rootCached race noExtras absent noFunction noVaList descriptor
    addressMode geometry exposed allocLive metadata notConstructed view destination
  refine ⟨converted,facts,?_⟩
  dsimp only at result ⊢
  rw [post_machine options frames _ borrowFrame machine global fresh id parentTag source converted ghost] at result
  simpa [ConcreteEmptyRootCopy.changedFrame,ConcreteEmptyReferenceArgumentCopy.copiedFrame,
    TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,Array.set_set] using result

end
end DuplicatePrefix.WildcardStaticEmptyRootCopy
