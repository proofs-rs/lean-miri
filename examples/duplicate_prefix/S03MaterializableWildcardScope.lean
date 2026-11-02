import duplicate_prefix.WildcardGlobalEmptyRootArgumentScope
import duplicate_prefix.WildcardStaticEmptyRootArgumentScope
import duplicate_prefix.DuplicatePrefixCallSpecification
import duplicate_prefix.WildcardPoolHitRootArgumentScope
import duplicate_prefix.ScopedFrame
namespace DuplicatePrefix.S03MaterializableWildcardScope
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts RootFrameData EmptyRootArguments ActualReferenceContext ConcreteEmptyRootArguments
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def resultMachine (options : EvalConfigurationCore.Options)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615) (id : AllocId)
    (parent : BorTag) (source : Allocation CtfeProvenance Unit) (converted : Allocation Provenance Unit) :=
  WildcardPoolHitRootArgumentScope.resultMachine (WildcardGlobalEmptyRootCopy.preparedMachine options machine id parent source converted)
    tracker fresh id (WildcardGlobalEmptyRootCopy.entry parent source converted) (WildcardGlobalEmptyReferenceReborrow.rootSlot parent source.byteSize)

/-- Both supported descriptor alternatives use the actual wildcard resolver,
materialization and zero-byte FnEntry, retaining full relocation support. -/
theorem scope
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (actualPointers : ctx.pointers = GlobalDataOnlyActualConfig.pointers PreparedReflection.actual.compiler
      PreparedReflection.actual.image (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions) ())
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (parentTag : BorTag) (tracker : MachineHooks.BorrowState)
    (base offset n : UInt64) (nonzero : base+offset ≠ 0)
    (frames : Array CompilerFrameContext.ActualFrame) (root : RootFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (dead1 : (root.frame.locals[1]'(root.valid i1)).value = .dead)
    (cache1 : (root.frame.locals[1]'(root.valid i1)).layout = none)
    (dead2 : (root.frame.locals[2]'(root.valid i2)).value = .dead)
    (cache2 : (root.frame.locals[2]'(root.valid i2)).layout = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (borrowFrame : FrameState) (frameBorrow : root.frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (distinct : parentTag ≠ tracker.global.nextPointerTag)
    (source : Allocation CtfeProvenance Unit) (supported : GlobalSupportedImage.Supported source PreparedReflection.actual.compiler.runtime.target
      machine.memory tracker.global.rootPointerTags machine.user.addresses.baseAddr)
    (rootCached : tracker.global.rootTag? id = some parentTag) (race : machine.dataRace = none)
    (noExtras : (machine.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id)) = false)
    (absent : machine.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : machine.memory.hasFunctionPointer id = false) (noVaList : machine.memory.hasVaListId id = false)
    (descriptor : DuplicatePrefixEmptyReferenceInput.ImageDescriptor
      (DuplicatePrefixCallSpecification.imageContext options machine tracker) machine.memory id source)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (geometry : WildcardGeneralHitReborrow.Geometry machine.user.addresses.intToPtrMap (base+offset) base id source.byteSize)
    (exposed : machine.user.addresses.exposed.contains id = true)
    (allocLive : machine.memory.isAllocLive id = true)
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false) :
    ∃ converted : Allocation Provenance Unit, GlobalAllocationAttributes.Attributes source converted ∧
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new .wildcard (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
      (RootCallCore.argumentBody (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
        ⟨.immediate value,ActualReferenceMetadata.reference⟩ (second n)) (Storage.withCurrent frames root.frame machine) =
      .ok (2,2) (Storage.withCurrent frames (RootArgumentsTwo.result (firstDone root adjusted borrowFrame id tracker.global.nextPointerTag) n).frame
        (resultMachine options machine tracker fresh id parentTag source converted)) := by
  rcases descriptor with memoryDescriptor | ⟨definition,initializer,staticDescriptor⟩
  · exact WildcardGlobalEmptyRootArgumentScope.scope options limits remaining span ctx actualPointers debugOff cmp dynamicFuel
      validityFuel fuelEq validationEq id parentTag tracker base offset n nonzero frames root machine dead1 cache1 dead2 cache2
      ghost shallow cachedAddress borrowFrame frameBorrow enabled fresh distinct source supported rootCached race noExtras absent
      noFunction noVaList memoryDescriptor addressMode geometry exposed allocLive metadata notConstructed
  · exact WildcardStaticEmptyRootArgumentScope.scope options limits remaining span ctx actualPointers debugOff cmp dynamicFuel
      validityFuel fuelEq validationEq id parentTag tracker base offset n nonzero frames root machine dead1 cache1 dead2 cache2
      ghost shallow cachedAddress borrowFrame frameBorrow enabled fresh distinct source definition initializer supported rootCached
      race noExtras absent noFunction noVaList staticDescriptor addressMode geometry exposed allocLive metadata notConstructed
end
end DuplicatePrefix.S03MaterializableWildcardScope
