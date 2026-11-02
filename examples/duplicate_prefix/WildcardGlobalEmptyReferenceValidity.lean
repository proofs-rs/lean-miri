import duplicate_prefix.WildcardGlobalEmptyReferencePointer
import duplicate_prefix.WildcardHitReferenceValidity

namespace DuplicatePrefix.WildcardGlobalEmptyReferenceValidity
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

theorem validate_global (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (actualPointers : ctx.pointers = GlobalDataOnlyActualConfig.pointers PreparedReflection.actual.compiler
      PreparedReflection.actual.image (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions) ())
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel + 1)
    (id : AllocId) (parentTag : BorTag) (global : GlobalState)
    (base offset : UInt64) (nonzero : base + offset ≠ 0)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new .wildcard (Size.ofBytes (base + offset))) 0 reference).imm))
    (cached : frame.locals[localId].layout = some reference)
    (ghost : machine.user.payload.ghost = false)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some ⟨global, .FnEntry⟩)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (distinct : parentTag ≠ global.nextPointerTag)
    (source : Allocation CtfeProvenance Unit) (supported : GlobalSupportedImage.Supported source PreparedReflection.actual.compiler.runtime.target
      machine.memory global.rootPointerTags machine.user.addresses.baseAddr)
    (rootCached : global.rootTag? id = some parentTag)
    (race : machine.dataRace = none)
    (noExtras : (machine.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id)) = false)
    (absent : machine.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : machine.memory.hasFunctionPointer id = false)
    (noVaList : machine.memory.hasVaListId id = false)
    (descriptor : machine.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (geometry : WildcardGeneralHitReborrow.Geometry machine.user.addresses.intToPtrMap (base+offset) base id source.byteSize)
    (exposed : machine.user.addresses.exposed.contains id = true)
    (allocLive : machine.memory.isAllocLive id = true)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any
      (·.value.ty == 4) = false)
    : ∃ converted : Allocation Provenance Unit,
      GlobalAllocationAttributes.Attributes source converted ∧
      let afterFrame := TypedBorrowSteps.registeredFrame frame borrowFrame id global.nextPointerTag
      let afterMachine := (WildcardGlobalEmptyReferencePointer.resultState options frames frame borrowFrame
        {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
        ⟨global,.FnEntry⟩ fresh id parentTag source converted).machine
    ValidityVisitor.validatePlace (config options remaining span).validity () (validityFuel + 1)
      (LocalPlaces.localRuntimePlace frames.size frame localId reference) false true
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {afterFrame with locals := (afterFrame.locals.set localId
          {value := .live (.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
            (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base + offset))) 0 reference).imm),
           layout := (afterFrame.locals[localId]'(by simpa [afterFrame,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow] using valid)).layout}
          (by simpa [afterFrame,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow] using valid))}
        {afterMachine with user := {afterMachine.user with payload := {afterMachine.user.payload with ghost := false}}}) := by
  let cfg := config options remaining span
  let retag := adapted options remaining span ctx.pointers
  let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
  let active := Storage.withCurrent frames frame activeMachine
  let place := RetagReferencePlace.slicePlace
    (Pointer.new .wildcard (Size.ofBytes (base + offset))) 0 pointee
  have fields := actual_fields options () remaining span
  have width : cfg.access.runtime.base.pointerWidth = .w64 := by rw [fields.accessRuntime]; rfl
  have debug : ctx.inner.debugAssertions = false := ctx.innerDebug.trans (fields.debug.trans debugOff)
  have noDebug : ctx.inner.debugAbiCheck
      (RetagReferencePlace.sliceValue cfg.access.runtime.base
        (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base + offset))) 0 reference).imm reference = pure () := by
    rw [ctx.innerAbi, fields.debugAbiNoChecks debugOff]
  have retain := actual_retain_touched options () remaining span
  have queries := reference_queries options remaining span ctx.pointers
  obtain ⟨target, tail, inhabited, name, classified⟩ := visitor_metadata options remaining span
  have tail' : cfg.validity.metadataTail () pointee.ty = pure .sliceOrStr := by rw [pointee_ty]; exact tail
  have inhabited' : cfg.validity.opsemInhabited () pointee.ty = pure true := by rw [pointee_ty]; exact inhabited
  have name' : cfg.validity.typeName () reference.ty = pure "&mut [u8]" := by rw [reference_ty]; exact name
  have classified' : cfg.validity.classify () reference.ty = pure (.reference true) := by rw [reference_ty]; exact classified
  have sizing : retag.sizeAndAlign place active = .ok (some (Size.ofBytes 0, Align.ONE)) active := by
    rw [← ctx.visitor.sizing]
    exact ProjectionMetadataFacts.actual_validity_size_at options remaining span cmp active dynamicFuel fuelEq 0
      metadata notConstructed (by decide) place rfl rfl
  obtain ⟨converted,facts,driver⟩ := WildcardGlobalEmptyReferencePointer.retag_pointer options remaining span ctx actualPointers
    cmp dynamicFuel fuelEq frames frame borrowFrame frameBorrow activeMachine ⟨global,.FnEntry⟩ enabled fresh
    id parentTag base offset cachedAddress distinct rootCached source supported race noExtras absent noFunction noVaList
    descriptor addressMode geometry exposed allocLive metadata notConstructed
  let afterFrame := TypedBorrowSteps.registeredFrame frame borrowFrame id global.nextPointerTag
  let afterMachine := (WildcardGlobalEmptyReferencePointer.resultState options frames frame borrowFrame activeMachine
    ⟨global,.FnEntry⟩ fresh id parentTag source converted).machine
  have sameLocals : afterFrame.locals = frame.locals := rfl
  have sameDestination : LocalPlaces.localRuntimePlace frames.size frame localId reference =
      LocalPlaces.localRuntimePlace frames.size afterFrame localId reference := rfl
  have ghostAfter : afterMachine.user.payload.ghost = true := rfl
  have afterState : WildcardGlobalEmptyReferencePointer.resultState options frames frame borrowFrame activeMachine
      ⟨global,.FnEntry⟩ fresh id parentTag source converted = Storage.withCurrent frames afterFrame afterMachine := rfl
  refine ⟨converted,facts,?_⟩
  have retagged : cfg.validity.retagPointer ()
      (RetagReferencePlace.sliceValue cfg.access.runtime.base
        (Pointer.new .wildcard (Size.ofBytes (base + offset))) 0 reference) reference.ty active =
      .ok (some (RetagReferencePlace.sliceValue cfg.access.runtime.base
        (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base + offset))) 0 reference))
        (Storage.withCurrent frames afterFrame afterMachine) := by
    rw [ctx.visitor.retagAction]
    unfold TypedRetag.machineRetagPtrValue
    simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, active, activeMachine,
      Storage.withCurrent, enabled]
    have result : TypedRetag.retagPtrValue retag options.limits.retag
        (RetagReferencePlace.sliceValue cfg.access.runtime.base
          (Pointer.new .wildcard (Size.ofBytes (base + offset))) 0 reference) reference.ty .FnEntry active =
        .ok (some (RetagReferencePlace.sliceValue cfg.access.runtime.base
          (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base + offset))) 0 reference))
          (WildcardGlobalEmptyReferencePointer.resultState options frames frame borrowFrame activeMachine
            ⟨global,.FnEntry⟩ fresh id parentTag source converted) := driver
    rw [afterState] at result
    rw [← enabled]
    exact result
  obtain ⟨pa, pb, ra, rb, pairOffset, repr⟩ := reference_repr
  exact WildcardHitReferenceValidity.validate_of_retag cfg.validity cfg.access cfg.allocation ctx.inner retag
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts ctx.pointers () options.limits.retag validityFuel
    ctx.visitor ctx.source reference pointee id global.nextPointerTag (base+offset) nonzero queries
    (by rw [reference_ty, pointee_ty]; exact RootMetadataQueries.mutable_slice_dereference)
    (by rw [pointee_ty]; exact pointee_layout)
    ProjectionMetadataFacts.slice_layout_shape.2.2 ctx.pointer width (visitor_target options remaining span).1
    (visitor_target options remaining span).2 ProjectionMetadataFacts.slice_layout_shape.2.1 tail' inhabited'
    "&mut [u8]" frames frame machine localId valid live cached reference_sized pa pb ra rb pairOffset repr debug noDebug
    ghost retain afterFrame afterMachine sameLocals sameDestination ghostAfter sizing retagged name' classified'

theorem validate_runtime_global (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (actualPointers : ctx.pointers = GlobalDataOnlyActualConfig.pointers PreparedReflection.actual.compiler
      PreparedReflection.actual.image (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions) ())
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel + 1)
    (id : AllocId) (parentTag : BorTag) (global : GlobalState)
    (base offset : UInt64) (nonzero : base + offset ≠ 0)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new .wildcard (Size.ofBytes (base + offset))) 0 reference).imm))
    (cached : frame.locals[localId].layout = some reference)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some ⟨global, .FnEntry⟩)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (distinct : parentTag ≠ global.nextPointerTag)
    (source : Allocation CtfeProvenance Unit) (supported : GlobalSupportedImage.Supported source PreparedReflection.actual.compiler.runtime.target
      machine.memory global.rootPointerTags machine.user.addresses.baseAddr)
    (rootCached : global.rootTag? id = some parentTag)
    (race : machine.dataRace = none)
    (noExtras : (machine.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id)) = false)
    (absent : machine.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : machine.memory.hasFunctionPointer id = false)
    (noVaList : machine.memory.hasVaListId id = false)
    (descriptor : machine.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (geometry : WildcardGeneralHitReborrow.Geometry machine.user.addresses.intToPtrMap (base+offset) base id source.byteSize)
    (exposed : machine.user.addresses.exposed.contains id = true)
    (allocLive : machine.memory.isAllocLive id = true)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any
      (·.value.ty == 4) = false)
    : ∃ converted : Allocation Provenance Unit,
      GlobalAllocationAttributes.Attributes source converted ∧
      let afterFrame := TypedBorrowSteps.registeredFrame frame borrowFrame id global.nextPointerTag
      let afterMachine := (WildcardGlobalEmptyReferencePointer.resultState options frames frame borrowFrame
        {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
        ⟨global,.FnEntry⟩ fresh id parentTag source converted).machine
    ValidityMachine.validateRuntime (config options remaining span).validity () (validityFuel + 1)
      (LocalPlaces.localRuntimePlace frames.size frame localId reference) true
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {afterFrame with locals := (afterFrame.locals.set localId
          {value := .live (.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
            (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base + offset))) 0 reference).imm),
           layout := (afterFrame.locals[localId]'(by simpa [afterFrame,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow] using valid)).layout}
          (by simpa [afterFrame,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow] using valid))}
        {afterMachine with user := {afterMachine.user with payload := {afterMachine.user.payload with ghost := false}}}) := by
  obtain ⟨converted,facts,checked⟩ := validate_global options remaining span ctx actualPointers debugOff cmp
    dynamicFuel validityFuel fuelEq id parentTag global base offset nonzero frames frame machine localId valid live
    cached ghost cachedAddress borrowFrame frameBorrow enabled fresh distinct source supported rootCached race noExtras
    absent noFunction noVaList descriptor addressMode geometry exposed allocLive metadata notConstructed
  refine ⟨converted,facts,?_⟩
  unfold ValidityMachine.validateRuntime
  simp only [ValidityMachine.enforceValidityRecursively,get,getThe,MonadStateOf.get,EStateM.get,
    bind,EStateM.bind,pure,EStateM.pure,Storage.withCurrent,shallow]
  have deep : (ValidityMachine.ValidationMode.Shallow == .Deep) = false := by decide
  simpa only [deep,Storage.withCurrent,shallow] using checked

end
end DuplicatePrefix.WildcardGlobalEmptyReferenceValidity
