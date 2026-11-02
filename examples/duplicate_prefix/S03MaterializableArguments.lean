import duplicate_prefix.S03MaterializableInput

namespace DuplicatePrefix.S03MaterializableArguments
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts RootFrameData EmptyRootArguments ActualReferenceContext ConcreteEmptyRootArguments
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- The actual concrete argument scope is derived from Materializable itself.
The returned packet retains the selected original image and supplies the
separate-return framing adapter. No successful materialization is assumed. -/
theorem concrete
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
    (candidate : DuplicatePrefixEmptyReferenceInput.Materializable (imageContext options machine tracker)
      machine.memory machine.user.addresses id (some parentTag))
    (below : ∀ row ∈ tracker.global.rootPointerTags.toList, row.2.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (race : machine.dataRace = none)
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false) :
    ∃ packet : S03MaterializableInput.Packet options machine tracker id (some parentTag),
      ∃ converted : Allocation Provenance Unit, GlobalAllocationAttributes.Attributes packet.source converted ∧
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
      (RootCallCore.argumentBody (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
        ⟨.immediate value,ActualReferenceMetadata.reference⟩ (second n)) (Storage.withCurrent frames root.frame machine) =
      .ok (2,2) (Storage.withCurrent frames (RootArgumentsTwo.result (firstDone root adjusted borrowFrame id tracker.global.nextPointerTag) n).frame
        (S03MaterializableArgumentScope.resultMachine options machine tracker fresh id packet.root packet.source converted)) := by
  obtain ⟨packet⟩ := S03MaterializableInput.of_input options machine tracker id (some parentTag) candidate below
  have same : parentTag = packet.root := by
    rcases packet.agreement with impossible | equal
    · cases impossible
    · exact Option.some.inj equal
  obtain ⟨converted,attributes,actual⟩ := S03MaterializableArgumentScope.scope options limits remaining span ctx actualPointers
    debugOff cmp dynamicFuel validityFuel fuelEq validationEq id packet.root tracker base offset n nonzero frames root machine
    dead1 cache1 dead2 cache2 ghost shallow cachedAddress borrowFrame frameBorrow enabled fresh packet.distinct packet.source
    packet.supported packet.rootCached race packet.noExtras packet.absent packet.noFunction packet.noVaList packet.descriptor
    metadata notConstructed
  exact ⟨packet,converted,attributes,by simpa only [same] using actual⟩

/-- Selected wildcard geometry is transported to the exact image size derived
from the descriptor, then the actual materialization/FnEntry scope executes. -/
theorem wildcard
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (actualPointers : ctx.pointers = GlobalDataOnlyActualConfig.pointers PreparedReflection.actual.compiler
      PreparedReflection.actual.image (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions) ())
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (tracker : MachineHooks.BorrowState)
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
    (candidate : DuplicatePrefixEmptyReferenceInput.Materializable (imageContext options machine tracker)
      machine.memory machine.user.addresses id none)
    (below : ∀ row ∈ tracker.global.rootPointerTags.toList, row.2.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (race : machine.dataRace = none)
    (info : AllocationInfo) (known : machine.memory.getAllocInfo id = .ok info)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (geometry : WildcardGeneralHitReborrow.Geometry machine.user.addresses.intToPtrMap (base+offset) base id info.size)
    (exposed : machine.user.addresses.exposed.contains id = true)
    (allocLive : machine.memory.isAllocLive id = true)
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false) :
    ∃ packet : S03MaterializableInput.Packet options machine tracker id none,
      ∃ converted : Allocation Provenance Unit, GlobalAllocationAttributes.Attributes packet.source converted ∧
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new .wildcard (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
      (RootCallCore.argumentBody (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
        ⟨.immediate value,ActualReferenceMetadata.reference⟩ (second n)) (Storage.withCurrent frames root.frame machine) =
      .ok (2,2) (Storage.withCurrent frames (RootArgumentsTwo.result (firstDone root adjusted borrowFrame id tracker.global.nextPointerTag) n).frame
        (S03MaterializableWildcardScope.resultMachine options machine tracker fresh id packet.root packet.source converted)) := by
  obtain ⟨packet⟩ := S03MaterializableInput.of_input options machine tracker id none candidate below
  have infoEq : info = ⟨packet.source.byteSize,packet.source.align,.liveData,packet.source.mutability⟩ :=
    Except.ok.inj (known.symm.trans packet.alloc_info)
  have size : info.size = packet.source.byteSize := congrArg AllocationInfo.size infoEq
  rw [size] at geometry
  obtain ⟨converted,attributes,actual⟩ := S03MaterializableWildcardScope.scope options limits remaining span ctx actualPointers
    debugOff cmp dynamicFuel validityFuel fuelEq validationEq id packet.root tracker base offset n nonzero frames root machine
    dead1 cache1 dead2 cache2 ghost shallow cachedAddress borrowFrame frameBorrow enabled fresh packet.distinct packet.source
    packet.supported packet.rootCached race packet.noExtras packet.absent packet.noFunction packet.noVaList packet.descriptor
    addressMode geometry exposed allocLive metadata notConstructed
  exact ⟨packet,converted,attributes,actual⟩

end
end DuplicatePrefix.S03MaterializableArguments
