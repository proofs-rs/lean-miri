import duplicate_prefix.WildcardHitReferenceBorrow
import duplicate_prefix.WildcardHitReferenceValidity
import duplicate_prefix.ActualPositiveReference

namespace DuplicatePrefix.ActualWildcardHitReference
open Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def finalTree (tree : BorrowTree) (tag : BorTag) : BorrowTree :=
  WildcardHitZeroConstructor.installed tree
    ⟨tree.tagMapping.mapping.push (tag,⟨UInt32.ofNat tree.tagMapping.mapping.size⟩),tree.tagMapping.deassigned⟩
    ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩ tag (.ReservedFrz false) .None

def resultState
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (borrowFrame : FrameState)
    (global : GlobalState) (fresh : global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) :=
  let tracker : MachineHooks.BorrowState := ⟨global,.FnEntry⟩
  Storage.withCurrent frames (TypedBorrowSteps.registeredFrame frame borrowFrame id global.nextPointerTag)
    { (TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
        (ReferenceBorrowDriver.allocatedTracker tracker fresh) global.nextPointerTag) with
      memory := RetagEntry.updatedMemory machine.memory id entry (finalTree entry.allocation.extra global.nextPointerTag) }

/-- Actual configured visitor retag action for an exposed exact-base live hit.
Compiler layout queries, allocation resolution, fresh tag allocation, protector
registration, wildcard-root insertion and concrete pointer reconstruction are
all derived. This is an entry component; no continuation safety is assumed. -/
theorem retag (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel + 1)
    (id : AllocId) (global : GlobalState) (base : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some ⟨global,.FnEntry⟩)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (inverse : machine.user.addresses.intToPtrMap = #[⟨base,id⟩])
    (exposed : machine.user.addresses.exposed.contains id = true)
    (tagMapFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping global.nextPointerTag)
    (noFree : entry.allocation.extra.tagMapping.deassigned.back? = none)
    (fits : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    (config options remaining span).validity.retagPointer ()
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new .wildcard (Size.ofBytes base)) 0 reference) reference.ty
      (Storage.withCurrent frames frame machine) =
      .ok (some (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes base)) 0 reference))
        (resultState frames frame machine borrowFrame global fresh id entry) := by
  let cfg := config options remaining span
  let adaptedRetag := adapted options remaining span ctx.pointers
  let place := RetagReferencePlace.slicePlace (Pointer.new .wildcard (Size.ofBytes base)) 0 pointee
  have queries := reference_queries options remaining span ctx.pointers
  have sizing : adaptedRetag.sizeAndAlign place (Storage.withCurrent frames frame machine) =
      .ok (some (Size.ofBytes 0,Align.ONE)) (Storage.withCurrent frames frame machine) := by
    rw [←ctx.visitor.sizing]
    exact ProjectionMetadataFacts.actual_validity_size_at options remaining span cmp _ dynamicFuel fuelEq 0
      metadata notConstructed (by decide) place rfl rfl
  have driver := WildcardHitReferenceBorrow.fnentry_pointer_append adaptedRetag
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts cfg.access cfg.validity.projection cfg.validity.vtable
    ctx.pointers () ctx.source options.limits.retag place frames frame borrowFrame machine ⟨global,.FnEntry⟩
    enabled fresh frameBorrow id entry base global.nextPointerTag rfl queries.freeze rfl ctx.resolve ctx.arithmetic cached
    ctx.globalKind ctx.globals ctx.ensure ctx.synchronize present addressMode inverse exposed tagMapFresh noFree fits
    reference queries.shape queries.pointee_eq queries.unpin queries.unsafeUnpin
    (by
      change CompilerFacts.builtinDeref _ reference.ty true = .ok (some pointee.ty)
      rw [reference_ty,pointee_ty]
      exact RootMetadataQueries.mutable_slice_dereference)
    (by
      change CompilerFacts.layoutOf _ pointee.ty = .ok pointee
      rw [pointee_ty]
      exact pointee_layout)
    ProjectionMetadataFacts.slice_layout_shape.2.2 rfl sizing
  rw [ctx.visitor.retagAction]
  unfold TypedRetag.machineRetagPtrValue
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,Storage.withCurrent,enabled]
  exact driver

theorem validate (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel + 1)
    (id : AllocId) (global : GlobalState)
    (base : UInt64) (nonzero : base ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new .wildcard (Size.ofBytes base)) 0 reference).imm))
    (cached : frame.locals[localId].layout = some reference)
    (ghost : machine.user.payload.ghost = false)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some ⟨global, .FnEntry⟩)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (inverse : machine.user.addresses.intToPtrMap = #[⟨base,id⟩])
    (exposed : machine.user.addresses.exposed.contains id = true)
    (tagMapFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping global.nextPointerTag)
    (noFree : entry.allocation.extra.tagMapping.deassigned.back? = none)
    (fits : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any
      (·.value.ty == 4) = false) :
    let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
    let afterFrame := TypedBorrowSteps.registeredFrame frame borrowFrame id global.nextPointerTag
    let afterMachine := (resultState frames frame activeMachine borrowFrame global fresh id entry).machine
    ValidityVisitor.validatePlace (config options remaining span).validity () (validityFuel + 1)
      (LocalPlaces.localRuntimePlace frames.size frame localId reference) false true
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {afterFrame with locals := (afterFrame.locals.set localId
          {value := .live (.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
            (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes base)) 0 reference).imm),
           layout := (afterFrame.locals[localId]'(by exact valid)).layout}
          (by exact valid))}
        {afterMachine with user := {afterMachine.user with payload := {afterMachine.user.payload with ghost := false}}}) := by
  dsimp only
  let afterFrame := TypedBorrowSteps.registeredFrame frame borrowFrame id global.nextPointerTag
  let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
  let afterMachine := (resultState frames frame activeMachine borrowFrame global fresh id entry).machine
  have sameLocals : afterFrame.locals = frame.locals := rfl
  have sameDestination : LocalPlaces.localRuntimePlace frames.size frame localId reference =
      LocalPlaces.localRuntimePlace frames.size afterFrame localId reference := rfl
  have ghostAfter : afterMachine.user.payload.ghost = true := rfl
  let cfg := config options remaining span
  let retag := adapted options remaining span ctx.pointers
  let active := Storage.withCurrent frames frame activeMachine
  let place := RetagReferencePlace.slicePlace
    (Pointer.new .wildcard (Size.ofBytes base)) 0 pointee
  have fields := actual_fields options () remaining span
  have width : cfg.access.runtime.base.pointerWidth = .w64 := by rw [fields.accessRuntime]; rfl
  have debug : ctx.inner.debugAssertions = false := ctx.innerDebug.trans (fields.debug.trans debugOff)
  have noDebug : ctx.inner.debugAbiCheck
      (RetagReferencePlace.sliceValue cfg.access.runtime.base
        (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes base)) 0 reference).imm reference = pure () := by
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
  have retagged := ActualWildcardHitReference.retag options remaining span ctx cmp dynamicFuel fuelEq
    id global base entry frames frame activeMachine borrowFrame frameBorrow enabled fresh cachedAddress present
    addressMode inverse exposed tagMapFresh noFree fits metadata notConstructed
  obtain ⟨pa, pb, ra, rb, pairOffset, repr⟩ := reference_repr
  exact WildcardHitReferenceValidity.validate_of_retag cfg.validity cfg.access cfg.allocation ctx.inner retag
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts ctx.pointers () options.limits.retag validityFuel
    ctx.visitor ctx.source reference pointee id global.nextPointerTag base nonzero queries
    (by rw [reference_ty, pointee_ty]; exact RootMetadataQueries.mutable_slice_dereference)
    (by rw [pointee_ty]; exact pointee_layout)
    ProjectionMetadataFacts.slice_layout_shape.2.2 ctx.pointer width (visitor_target options remaining span).1
    (visitor_target options remaining span).2 ProjectionMetadataFacts.slice_layout_shape.2.1 tail' inhabited'
    "&mut [u8]" frames frame machine localId valid live cached reference_sized pa pb ra rb pairOffset repr debug noDebug
    ghost retain afterFrame afterMachine sameLocals sameDestination ghostAfter sizing retagged name' classified'

theorem validate_runtime (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel + 1)
    (id : AllocId) (global : GlobalState)
    (base : UInt64) (nonzero : base ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new .wildcard (Size.ofBytes base)) 0 reference).imm))
    (cached : frame.locals[localId].layout = some reference)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some ⟨global, .FnEntry⟩)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (inverse : machine.user.addresses.intToPtrMap = #[⟨base,id⟩])
    (exposed : machine.user.addresses.exposed.contains id = true)
    (tagMapFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping global.nextPointerTag)
    (noFree : entry.allocation.extra.tagMapping.deassigned.back? = none)
    (fits : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any
      (·.value.ty == 4) = false) :
    let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
    let afterFrame := TypedBorrowSteps.registeredFrame frame borrowFrame id global.nextPointerTag
    let afterMachine := (resultState frames frame activeMachine borrowFrame global fresh id entry).machine
    ValidityMachine.validateRuntime (config options remaining span).validity () (validityFuel + 1)
      (LocalPlaces.localRuntimePlace frames.size frame localId reference) true
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {afterFrame with locals := (afterFrame.locals.set localId
          {value := .live (.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
            (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes base)) 0 reference).imm),
           layout := (afterFrame.locals[localId]'(by exact valid)).layout}
          (by exact valid))}
        {afterMachine with user := {afterMachine.user with payload := {afterMachine.user.payload with ghost := false}}}) := by
  have checked := validate options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq id global
    base nonzero entry frames frame machine localId valid live cached ghost cachedAddress present borrowFrame
    frameBorrow enabled fresh addressMode inverse exposed tagMapFresh noFree fits metadata notConstructed
  have shallowNotDeep : (ValidityMachine.ValidationMode.Shallow == .Deep) = false := by decide
  unfold ValidityMachine.validateRuntime
  simp only [ValidityMachine.enforceValidityRecursively,get,getThe,MonadStateOf.get,EStateM.get,
    bind,EStateM.bind,pure,EStateM.pure,Storage.withCurrent,shallow,shallowNotDeep]
  simpa only [Storage.withCurrent,resultState,ReferenceBorrowDriver.allocatedMachine,
    ReferenceBorrowDriver.allocatedTracker,TypedBorrowSteps.registeredMachine,shallow] using checked

end DuplicatePrefix.ActualWildcardHitReference
