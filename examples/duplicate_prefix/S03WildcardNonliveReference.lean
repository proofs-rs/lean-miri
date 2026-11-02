import duplicate_prefix.ActualConcreteEmptyReference
import duplicate_prefix.S03WildcardNonliveBorrow
import duplicate_prefix.WildcardHitReferenceValidity
namespace DuplicatePrefix.S03WildcardNonliveReference
open Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter
open Miri.TreeBorrows CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
abbrev nonliveRetagState := ActualConcreteEmptyReference.nonliveRetagState
theorem validate_nonlive (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel + 1)
    (id : AllocId) (global : GlobalState)
    (base offset : UInt64) (nonzero : base+offset ≠ 0)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new .wildcard (Size.ofBytes (base+offset))) 0 reference).imm))
    (cached : frame.locals[localId].layout = some reference)
    (ghost : machine.user.payload.ghost = false)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (info : AllocationInfo)
    (allocationInfo : machine.memory.getAllocInfo id = .ok info)
    (nonlive : info.kind ≠ .liveData)
    (geometry : WildcardGeneralHitReborrow.Geometry machine.user.addresses.intToPtrMap (base+offset) base id info.size)
    (nonstrict : machine.user.addresses.provenanceMode ≠ .strict)
    (exposed : machine.user.addresses.exposed.contains id = true)
    (allocLive : machine.memory.isAllocLive id = true)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some ⟨global, .FnEntry⟩)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any
      (·.value.ty == 4) = false)
    (afterFrame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (afterMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sameLocals : afterFrame.locals = frame.locals)
    (sameDestination : LocalPlaces.localRuntimePlace frames.size frame localId reference =
      LocalPlaces.localRuntimePlace frames.size afterFrame localId reference)
    (ghostAfter : afterMachine.user.payload.ghost = true)
    (afterState : nonliveRetagState frames frame machine borrowFrame global fresh id =
      Storage.withCurrent frames afterFrame afterMachine) :
    ValidityVisitor.validatePlace (config options remaining span).validity () (validityFuel + 1)
      (LocalPlaces.localRuntimePlace frames.size frame localId reference) false true
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {afterFrame with locals := (afterFrame.locals.set localId
          {value := .live (.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
            (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base+offset))) 0 reference).imm),
           layout := (afterFrame.locals[localId]'(by simpa [sameLocals] using valid)).layout}
          (by simpa [sameLocals] using valid))}
        {afterMachine with user := {afterMachine.user with payload := {afterMachine.user.payload with ghost := false}}}) := by
  let cfg := config options remaining span
  let retag := adapted options remaining span ctx.pointers
  let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
  let active := Storage.withCurrent frames frame activeMachine
  let place := RetagReferencePlace.slicePlace
    (Pointer.new .wildcard (Size.ofBytes (base+offset))) 0 pointee
  have fields := actual_fields options () remaining span
  have width : cfg.access.runtime.base.pointerWidth = .w64 := by rw [fields.accessRuntime]; rfl
  have debug : ctx.inner.debugAssertions = false := ctx.innerDebug.trans (fields.debug.trans debugOff)
  have noDebug : ctx.inner.debugAbiCheck
      (RetagReferencePlace.sliceValue cfg.access.runtime.base
        (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base+offset))) 0 reference).imm reference = pure () := by
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
  have driver := S03WildcardNonliveBorrow.nonlive_zero_reference_pointer retag
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts cfg.access cfg.validity.projection cfg.validity.vtable
    ctx.pointers () ctx.source options.limits.retag place frames frame borrowFrame activeMachine ⟨global, .FnEntry⟩
    enabled fresh frameBorrow id base offset global.nextPointerTag rfl
    ChildBorrow.fnEntryPolicy rfl queries.freeze rfl ctx.resolve ctx.arithmetic cachedAddress
    nonstrict exposed allocLive info allocationInfo nonlive geometry reference .Mut .FnEntry (by decide)
    queries.shape queries.pointee_eq queries.unpin queries.unsafeUnpin
    (by
      change CompilerFacts.builtinDeref _ reference.ty true = .ok (some pointee.ty)
      rw [reference_ty, pointee_ty]
      exact RootMetadataQueries.mutable_slice_dereference)
    (by
      change CompilerFacts.layoutOf _ pointee.ty = .ok pointee
      rw [pointee_ty]
      exact pointee_layout)
    ProjectionMetadataFacts.slice_layout_shape.2.2 rfl sizing
  have retagged : cfg.validity.retagPointer ()
      (RetagReferencePlace.sliceValue cfg.access.runtime.base
        (Pointer.new .wildcard (Size.ofBytes (base+offset))) 0 reference) reference.ty active =
      .ok (some (RetagReferencePlace.sliceValue cfg.access.runtime.base
        (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base+offset))) 0 reference))
        (Storage.withCurrent frames afterFrame afterMachine) := by
    rw [ctx.visitor.retagAction]
    unfold TypedRetag.machineRetagPtrValue
    simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, active, activeMachine,
      Storage.withCurrent, enabled]
    have result : TypedRetag.retagPtrValue retag options.limits.retag
        (RetagReferencePlace.sliceValue cfg.access.runtime.base
          (Pointer.new .wildcard (Size.ofBytes (base+offset))) 0 reference) reference.ty .FnEntry active =
        .ok (some (RetagReferencePlace.sliceValue cfg.access.runtime.base
          (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base+offset))) 0 reference))
          (nonliveRetagState frames frame machine borrowFrame global fresh id) := driver
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
theorem validate_runtime_nonlive (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel + 1)
    (id : AllocId) (global : GlobalState)
    (base offset : UInt64) (nonzero : base+offset ≠ 0)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new .wildcard (Size.ofBytes (base+offset))) 0 reference).imm))
    (cached : frame.locals[localId].layout = some reference)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (info : AllocationInfo)
    (allocationInfo : machine.memory.getAllocInfo id = .ok info)
    (nonlive : info.kind ≠ .liveData)
    (geometry : WildcardGeneralHitReborrow.Geometry machine.user.addresses.intToPtrMap (base+offset) base id info.size)
    (nonstrict : machine.user.addresses.provenanceMode ≠ .strict)
    (exposed : machine.user.addresses.exposed.contains id = true)
    (allocLive : machine.memory.isAllocLive id = true)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some ⟨global, .FnEntry⟩)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any
      (·.value.ty == 4) = false)
    (afterFrame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (afterMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sameLocals : afterFrame.locals = frame.locals)
    (sameDestination : LocalPlaces.localRuntimePlace frames.size frame localId reference =
      LocalPlaces.localRuntimePlace frames.size afterFrame localId reference)
    (ghostAfter : afterMachine.user.payload.ghost = true)
    (afterState : nonliveRetagState frames frame machine borrowFrame global fresh id =
      Storage.withCurrent frames afterFrame afterMachine) :
    ValidityMachine.validateRuntime (config options remaining span).validity () (validityFuel + 1)
      (LocalPlaces.localRuntimePlace frames.size frame localId reference) true
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {afterFrame with locals := (afterFrame.locals.set localId
          {value := .live (.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
            (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base+offset))) 0 reference).imm),
           layout := (afterFrame.locals[localId]'(by simpa [sameLocals] using valid)).layout}
          (by simpa [sameLocals] using valid))}
        {afterMachine with user := {afterMachine.user with payload := {afterMachine.user.payload with ghost := false}}}) := by
  have checked := validate_nonlive options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq id global base offset nonzero frames frame machine localId valid live cached ghost cachedAddress info allocationInfo nonlive geometry nonstrict exposed allocLive borrowFrame frameBorrow enabled fresh metadata notConstructed afterFrame afterMachine sameLocals sameDestination ghostAfter afterState
  unfold ValidityMachine.validateRuntime
  simp only [ValidityMachine.enforceValidityRecursively, get, getThe, MonadStateOf.get, EStateM.get,
    bind, EStateM.bind, pure, EStateM.pure, Storage.withCurrent, shallow]
  exact checked

end
end DuplicatePrefix.S03WildcardNonliveReference
