import duplicate_prefix.GeneralBorrowRawWildcardReferenceDriver
import duplicate_prefix.GeneralBorrowPositiveWildcardReferenceValidity
import duplicate_prefix.SharedReferenceValidity
import duplicate_prefix.ActualReferenceMetadata
import duplicate_prefix.SharedReferenceMetadata
namespace DuplicatePrefix.GeneralBorrowRawWildcardRuntimeValidator
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem positive
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (reference : LocalLayout)
    (shape : (adapted options remaining span ctx.pointers).typeShape reference.ty = pure .reference)
    (pointeeQuery : (adapted options remaining span ctx.pointers).referencePointee reference.ty =
      pure (ProjectionMetadataFacts.sliceLayout.ty,.Mut))
    (unpin : (adapted options remaining span ctx.pointers).isUnpin ProjectionMetadataFacts.sliceLayout.ty = pure true)
    (unsafeUnpin : (adapted options remaining span ctx.pointers).isUnsafeUnpin ProjectionMetadataFacts.sliceLayout.ty = pure true)
    (frozen : (adapted options remaining span ctx.pointers).typeIsFreeze ProjectionMetadataFacts.sliceLayout.ty = pure true)
    (dereference : CompilerFacts.builtinDeref ReferenceMetadataFacts.prepared.context reference.ty true =
      .ok (some ProjectionMetadataFacts.sliceLayout.ty))
    (sized : reference.layout.isSized = true)
    (readable : ∃ pa pb ra rb offset, reference.layout.backendRepr = .ScalarPair
      (a := .Initialized (value := pa) (validRange := ra)) (b := .Initialized (value := pb) (validRange := rb)) (bOffset := offset))
    (name : String)
    (named : (config options remaining span).validity.typeName () reference.ty = pure name)
    (classified : (config options remaining span).validity.classify () reference.ty = pure (.reference true))
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base len : UInt64)
    (positive : (0 : UInt64) < len) (nonzero : base ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (currentMode : tracker.retagMode = .FnEntry)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base (Pointer.new .wildcard (Size.ofBytes (base))) len reference).imm))
    (cached : frame.locals[localId].layout = some reference)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (position : Nat) (positionValid : position < machine.user.addresses.intToPtrMap.size)
    (ordered : WildcardInteriorHitAddress.Ordered machine.user.addresses.intToPtrMap)
    (addressRow : machine.user.addresses.intToPtrMap[position]? = some ⟨base,id⟩)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (exposedAlloc : machine.user.addresses.exposed.contains id = true)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (capability : DuplicatePrefixBorrowAuthorization.Positive entry.allocation.extra tracker.global.protectedTags none none none 0 len)
    (distinct : entry.allocation.extra.roots.toList.Nodup)
    (short : entry.allocation.extra.nodes.size < 65536)
    (nodeRoom : entry.allocation.extra.nodes.size+1 ≤ 4294967295)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    ∃ output : GeneralBorrowForestFnEntry.Output,
      GeneralBorrowRawWildcardFnEntryRuntime.operation entry.allocation.extra tracker.global borrowFrame id 0 len = .ok output ∧
    let cfg := config options remaining span
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry output.child.tree}
    ValidityMachine.validateRuntime cfg.validity () (validityFuel+1)
      (LocalPlaces.localRuntimePlace frames.size frame localId reference) true (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames {(TypedBorrowSteps.registeredFrame frame borrowFrame id tracker.global.nextPointerTag) with locals := (frame.locals.set localId
        {value := .live (.immediate (RetagReferencePlace.sliceValue cfg.access.runtime.base
          (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base))) len reference).imm),
         layout := frame.locals[localId].layout} valid)} resultMachine) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      ∃ child,output.child.tree.indexOfTag tracker.global.nextPointerTag = some child ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive output.child.tree output.global.protectedTags
          (some child) (some child) (some tracker.global.nextPointerTag) 0 len) := by
  let cfg := config options remaining span
  let retag := adapted options remaining span ctx.pointers
  let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
  let active := Storage.withCurrent frames frame activeMachine
  let place := RetagReferencePlace.slicePlace (Pointer.new (Provenance.wildcard) (Size.ofBytes (base))) len ProjectionMetadataFacts.sliceLayout
  let registeredFrame := TypedBorrowSteps.registeredFrame frame borrowFrame id tracker.global.nextPointerTag
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have bounded : len ≤ 9223372036854775807 := by
    apply UInt64.le_iff_toNat_le.mpr
    change len.toNat ≤ 9223372036854775807
    omega
  have sizing : retag.sizeAndAlign place active = .ok (some (Size.ofBytes len,Align.ONE)) active := by
    rw [← ctx.visitor.sizing]
    exact ProjectionMetadataFacts.actual_validity_size_at options remaining span cmp active dynamicFuel fuelEq len
      metadata notConstructed bounded place rfl rfl
  obtain ⟨output,run,retagged,afterRuntime,child,lookup,both⟩ := GeneralBorrowRawWildcardReferenceDriver.pointer retag ReferenceMetadataFacts.prepared cfg.access
    cfg.validity.projection cfg.validity.vtable ctx.pointers () ctx.source options.limits.retag place frames frame borrowFrame activeMachine
    tracker enabled frameBorrow fresh base len id entry positive signedFits bounds rfl ctx.resolve ctx.arithmetic
    position positionValid ordered addressRow addressMode exposedAlloc cachedAddress present race ctx.globalKind ctx.globals
    ctx.ensure ctx.synchronize frozen sizing runtime capability distinct short nodeRoom reference shape pointeeQuery unpin unsafeUnpin dereference ActualReferenceMetadata.pointee_layout
    ProjectionMetadataFacts.slice_layout_shape.2.2 rfl
  let afterMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine activeMachine tracker fresh)
    (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
    memory := RetagEntry.updatedMemory machine.memory id entry output.child.tree}
  have retagAt : cfg.validity.retagPointer () (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new .wildcard (Size.ofBytes (base))) len reference) reference.ty active =
      .ok (some (RetagReferencePlace.sliceValue cfg.access.runtime.base
        (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base))) len reference))
        (Storage.withCurrent frames registeredFrame afterMachine) := by
    rw [ctx.visitor.retagAction]
    unfold TypedRetag.machineRetagPtrValue
    simp only [active,activeMachine,Storage.withCurrent,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,
      enabled,currentMode]
    simpa only [retag,activeMachine,afterMachine,Storage.withCurrent,enabled] using retagged
  have debug : ctx.inner.debugAssertions = false := ctx.innerDebug.trans (fields.debug.trans debugOff)
  have noDebug : ctx.inner.debugAbiCheck (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base))) len reference).imm reference = pure () := by
    rw [ctx.innerAbi,fields.debugAbiNoChecks debugOff]
  obtain ⟨target,tail,inhabited,name3,kind3⟩ := ActualReferenceMetadata.visitor_metadata options remaining span
  obtain ⟨pa,pb,ra,rb,pairOffset,repr⟩ := readable
  have validator := GeneralBorrowPositiveWildcardReferenceValidity.reference_validate_of_retag cfg.validity cfg.access cfg.allocation ctx.inner retag
    ReferenceMetadataFacts.prepared ctx.pointers () options.limits.retag validityFuel ctx.visitor ctx.source reference
    ProjectionMetadataFacts.sliceLayout id tracker.global.nextPointerTag base len nonzero entry ctx.resolve ctx.arithmetic
    positive signedFits bounds dereference ActualReferenceMetadata.pointee_layout ProjectionMetadataFacts.slice_layout_shape.2.2
    ctx.pointer (CanonicalConfigFacts.actual_target_width options () remaining span)
    (ActualReferenceMetadata.visitor_target options remaining span).1 (ActualReferenceMetadata.visitor_target options remaining span).2
    ProjectionMetadataFacts.slice_layout_shape.2.1 tail inhabited name true frames frame machine localId valid live cached sized
    pa pb ra rb pairOffset repr debug noDebug ghost (CanonicalConfigFacts.actual_retain_touched options () remaining span)
    cachedAddress present position positionValid ordered addressRow addressMode exposedAlloc registeredFrame afterMachine rfl rfl rfl sizing retagAt named classified
  have recursive : ValidityMachine.enforceValidityRecursively (Storage.withCurrent frames frame machine) =
      .ok false (Storage.withCurrent frames frame machine) := by
    simp [ValidityMachine.enforceValidityRecursively,Storage.withCurrent,shallow,
      get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
  refine ⟨output,run,?_,afterRuntime,child,lookup,both⟩
  unfold ValidityMachine.validateRuntime
  simp only [bind,EStateM.bind,recursive]
  have restore : {machine.user.payload with ghost := false} = machine.user.payload := by rw [← ghost]
  simpa only [afterMachine,activeMachine,ReferenceBorrowDriver.allocatedMachine,TypedBorrowSteps.registeredMachine,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,registeredFrame,restore] using validator

end
end DuplicatePrefix.GeneralBorrowRawWildcardRuntimeValidator
