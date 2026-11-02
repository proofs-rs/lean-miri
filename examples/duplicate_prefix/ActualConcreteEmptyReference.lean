import duplicate_prefix.ActualPositiveReference
import duplicate_prefix.ConcreteEmptyReferenceBorrow
import duplicate_prefix.ConcreteEmptyReferenceValidity
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.ActualConcreteEmptyReference
open Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter
open Miri.TreeBorrows CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata
noncomputable section

def liveRetagState (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (borrowFrame : FrameState)
    (global : GlobalState) (fresh : global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (parentTag : BorTag) (capacity : UInt64) :=
  let active := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
  let tracker : MachineHooks.BorrowState := ⟨global, .FnEntry⟩
  Storage.withCurrent frames (TypedBorrowSteps.registeredFrame frame borrowFrame id global.nextPointerTag)
    {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine active tracker fresh)
        (ReferenceBorrowDriver.allocatedTracker tracker fresh) global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry
        (TypedRetagConcreteEmpty.lazyTree parentTag global.nextPointerTag capacity)}

def nonliveRetagState (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (borrowFrame : FrameState)
    (global : GlobalState) (fresh : global.nextPointerTag.value < 18446744073709551615) (id : AllocId) :=
  let active := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
  let tracker : MachineHooks.BorrowState := ⟨global, .FnEntry⟩
  Storage.withCurrent frames (TypedBorrowSteps.registeredFrame frame borrowFrame id global.nextPointerTag)
    (TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine active tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) global.nextPointerTag)

theorem validate_live (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel + 1)
    (id : AllocId) (parentTag : BorTag) (global : GlobalState)
    (base offset capacity : UInt64) (nonzero : base + offset ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + offset))) 0 reference).imm))
    (cached : frame.locals[localId].layout = some reference)
    (ghost : machine.user.payload.ghost = false)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some ⟨global, .FnEntry⟩)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (distinct : parentTag ≠ global.nextPointerTag)
    (root : entry.allocation.extra = BorrowTree.new parentTag (Size.ofBytes capacity))
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
    (afterState : liveRetagState frames frame machine borrowFrame global fresh id entry parentTag capacity =
      Storage.withCurrent frames afterFrame afterMachine) :
    ValidityVisitor.validatePlace (config options remaining span).validity () (validityFuel + 1)
      (LocalPlaces.localRuntimePlace frames.size frame localId reference) false true
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {afterFrame with locals := (afterFrame.locals.set localId
          {value := .live (.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
            (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base + offset))) 0 reference).imm),
           layout := (afterFrame.locals[localId]'(by simpa [sameLocals] using valid)).layout}
          (by simpa [sameLocals] using valid))}
        {afterMachine with user := {afterMachine.user with payload := {afterMachine.user.payload with ghost := false}}}) := by
  let cfg := config options remaining span
  let retag := adapted options remaining span ctx.pointers
  let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
  let active := Storage.withCurrent frames frame activeMachine
  let place := RetagReferencePlace.slicePlace
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + offset))) 0 pointee
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
  have child : entry.allocation.extra.newChild (Size.ofBytes offset) (.concrete parentTag) global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new Size.ZERO ChildBorrow.fnEntryLocation)
      ChildBorrow.fnEntryPolicy.outsidePermission ChildBorrow.fnEntryPolicy.protector.isSome =
      ⟨TypedRetagConcreteEmpty.lazyTree parentTag global.nextPointerTag capacity, .ok ()⟩ := by
    rw [root]
    exact ChildConstructor.new_child_zero_exact parentTag global.nextPointerTag distinct capacity offset
  have driver := ConcreteEmptyReferenceBorrow.live_zero_reference_pointer retag
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts cfg.access cfg.validity.projection cfg.validity.vtable
    ctx.pointers () ctx.source options.limits.retag place frames frame borrowFrame activeMachine ⟨global, .FnEntry⟩
    enabled fresh frameBorrow id entry base offset parentTag global.nextPointerTag rfl ChildBorrow.fnEntryLocation
    ChildBorrow.fnEntryPolicy rfl queries.freeze (ChildBorrow.mutable_fn_entry_initial_location true) rfl
    ctx.resolve ctx.arithmetic cachedAddress ctx.globalKind ctx.globals ctx.ensure ctx.synchronize present
    (TypedRetagConcreteEmpty.lazyTree parentTag global.nextPointerTag capacity) child reference .Mut .FnEntry
    (by decide) queries.shape queries.pointee_eq queries.unpin queries.unsafeUnpin
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
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + offset))) 0 reference) reference.ty active =
      .ok (some (RetagReferencePlace.sliceValue cfg.access.runtime.base
        (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base + offset))) 0 reference))
        (Storage.withCurrent frames afterFrame afterMachine) := by
    rw [ctx.visitor.retagAction]
    unfold TypedRetag.machineRetagPtrValue
    simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, active, activeMachine,
      Storage.withCurrent, enabled]
    have result : TypedRetag.retagPtrValue retag options.limits.retag
        (RetagReferencePlace.sliceValue cfg.access.runtime.base
          (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + offset))) 0 reference) reference.ty .FnEntry active =
        .ok (some (RetagReferencePlace.sliceValue cfg.access.runtime.base
          (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base + offset))) 0 reference))
          (liveRetagState frames frame machine borrowFrame global fresh id entry parentTag capacity) := driver
    rw [afterState] at result
    rw [← enabled]
    exact result
  obtain ⟨pa, pb, ra, rb, pairOffset, repr⟩ := reference_repr
  exact ConcreteEmptyReferenceValidity.validate_of_retag cfg.validity cfg.access cfg.allocation ctx.inner retag
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts ctx.pointers () options.limits.retag validityFuel
    ctx.visitor ctx.source reference pointee id parentTag global.nextPointerTag base offset nonzero queries
    (by rw [reference_ty, pointee_ty]; exact RootMetadataQueries.mutable_slice_dereference)
    (by rw [pointee_ty]; exact pointee_layout)
    ProjectionMetadataFacts.slice_layout_shape.2.2 ctx.pointer width (visitor_target options remaining span).1
    (visitor_target options remaining span).2 ProjectionMetadataFacts.slice_layout_shape.2.1 tail' inhabited'
    "&mut [u8]" frames frame machine localId valid live cached reference_sized pa pb ra rb pairOffset repr debug noDebug
    ghost retain afterFrame afterMachine sameLocals sameDestination ghostAfter sizing retagged name' classified'

theorem validate_nonlive (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
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
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + offset))) 0 reference).imm))
    (cached : frame.locals[localId].layout = some reference)
    (ghost : machine.user.payload.ghost = false)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some ⟨global, .FnEntry⟩)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (info : AllocationInfo)
    (allocationInfo : machine.memory.getAllocInfo id = .ok info)
    (nonlive : info.kind ≠ .liveData)
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
            (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base + offset))) 0 reference).imm),
           layout := (afterFrame.locals[localId]'(by simpa [sameLocals] using valid)).layout}
          (by simpa [sameLocals] using valid))}
        {afterMachine with user := {afterMachine.user with payload := {afterMachine.user.payload with ghost := false}}}) := by
  let cfg := config options remaining span
  let retag := adapted options remaining span ctx.pointers
  let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
  let active := Storage.withCurrent frames frame activeMachine
  let place := RetagReferencePlace.slicePlace
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + offset))) 0 pointee
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
  have driver := ConcreteEmptyReferenceBorrow.nonlive_zero_reference_pointer retag
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts cfg.access cfg.validity.projection cfg.validity.vtable
    ctx.pointers () ctx.source options.limits.retag place frames frame borrowFrame activeMachine ⟨global, .FnEntry⟩
    enabled fresh frameBorrow id base offset parentTag global.nextPointerTag rfl
    ChildBorrow.fnEntryPolicy rfl queries.freeze rfl ctx.resolve ctx.arithmetic cachedAddress
    info allocationInfo nonlive reference .Mut .FnEntry (by decide)
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
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + offset))) 0 reference) reference.ty active =
      .ok (some (RetagReferencePlace.sliceValue cfg.access.runtime.base
        (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base + offset))) 0 reference))
        (Storage.withCurrent frames afterFrame afterMachine) := by
    rw [ctx.visitor.retagAction]
    unfold TypedRetag.machineRetagPtrValue
    simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, active, activeMachine,
      Storage.withCurrent, enabled]
    have result : TypedRetag.retagPtrValue retag options.limits.retag
        (RetagReferencePlace.sliceValue cfg.access.runtime.base
          (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + offset))) 0 reference) reference.ty .FnEntry active =
        .ok (some (RetagReferencePlace.sliceValue cfg.access.runtime.base
          (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base + offset))) 0 reference))
          (nonliveRetagState frames frame machine borrowFrame global fresh id) := driver
    rw [afterState] at result
    rw [← enabled]
    exact result
  obtain ⟨pa, pb, ra, rb, pairOffset, repr⟩ := reference_repr
  exact ConcreteEmptyReferenceValidity.validate_of_retag cfg.validity cfg.access cfg.allocation ctx.inner retag
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts ctx.pointers () options.limits.retag validityFuel
    ctx.visitor ctx.source reference pointee id parentTag global.nextPointerTag base offset nonzero queries
    (by rw [reference_ty, pointee_ty]; exact RootMetadataQueries.mutable_slice_dereference)
    (by rw [pointee_ty]; exact pointee_layout)
    ProjectionMetadataFacts.slice_layout_shape.2.2 ctx.pointer width (visitor_target options remaining span).1
    (visitor_target options remaining span).2 ProjectionMetadataFacts.slice_layout_shape.2.1 tail' inhabited'
    "&mut [u8]" frames frame machine localId valid live cached reference_sized pa pb ra rb pairOffset repr debug noDebug
    ghost retain afterFrame afterMachine sameLocals sameDestination ghostAfter sizing retagged name' classified'

theorem validate_runtime_live (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel + 1)
    (id : AllocId) (parentTag : BorTag) (global : GlobalState)
    (base offset capacity : UInt64) (nonzero : base + offset ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + offset))) 0 reference).imm))
    (cached : frame.locals[localId].layout = some reference)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some ⟨global, .FnEntry⟩)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (distinct : parentTag ≠ global.nextPointerTag)
    (root : entry.allocation.extra = BorrowTree.new parentTag (Size.ofBytes capacity))
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
    (afterState : liveRetagState frames frame machine borrowFrame global fresh id entry parentTag capacity =
      Storage.withCurrent frames afterFrame afterMachine) :
    ValidityMachine.validateRuntime (config options remaining span).validity () (validityFuel + 1)
      (LocalPlaces.localRuntimePlace frames.size frame localId reference) true
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {afterFrame with locals := (afterFrame.locals.set localId
          {value := .live (.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
            (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base + offset))) 0 reference).imm),
           layout := (afterFrame.locals[localId]'(by simpa [sameLocals] using valid)).layout}
          (by simpa [sameLocals] using valid))}
        {afterMachine with user := {afterMachine.user with payload := {afterMachine.user.payload with ghost := false}}}) := by
  have checked := validate_live options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq id parentTag global base offset capacity nonzero entry frames frame machine localId valid live cached ghost cachedAddress present borrowFrame frameBorrow enabled fresh distinct root metadata notConstructed afterFrame afterMachine sameLocals sameDestination ghostAfter afterState
  unfold ValidityMachine.validateRuntime
  simp only [ValidityMachine.enforceValidityRecursively, get, getThe, MonadStateOf.get, EStateM.get,
    bind, EStateM.bind, pure, EStateM.pure, Storage.withCurrent, shallow]
  exact checked

theorem validate_runtime_nonlive (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
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
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + offset))) 0 reference).imm))
    (cached : frame.locals[localId].layout = some reference)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some ⟨global, .FnEntry⟩)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (info : AllocationInfo)
    (allocationInfo : machine.memory.getAllocInfo id = .ok info)
    (nonlive : info.kind ≠ .liveData)
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
            (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base + offset))) 0 reference).imm),
           layout := (afterFrame.locals[localId]'(by simpa [sameLocals] using valid)).layout}
          (by simpa [sameLocals] using valid))}
        {afterMachine with user := {afterMachine.user with payload := {afterMachine.user.payload with ghost := false}}}) := by
  have checked := validate_nonlive options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq id parentTag global base offset nonzero frames frame machine localId valid live cached ghost cachedAddress borrowFrame frameBorrow enabled fresh info allocationInfo nonlive metadata notConstructed afterFrame afterMachine sameLocals sameDestination ghostAfter afterState
  unfold ValidityMachine.validateRuntime
  simp only [ValidityMachine.enforceValidityRecursively, get, getThe, MonadStateOf.get, EStateM.get,
    bind, EStateM.bind, pure, EStateM.pure, Storage.withCurrent, shallow]
  exact checked

theorem live_poststate
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (borrowFrame : FrameState) (global : GlobalState)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (parentTag : BorTag) (capacity : UInt64) (localId : Miri.MIR.LocalId) :
    ∃ afterFrame afterMachine,
      liveRetagState frames frame machine borrowFrame global fresh id entry parentTag capacity =
        Storage.withCurrent frames afterFrame afterMachine ∧
      afterFrame.locals = frame.locals ∧
      LocalPlaces.localRuntimePlace frames.size frame localId reference =
        LocalPlaces.localRuntimePlace frames.size afterFrame localId reference ∧
      afterMachine.user.payload.ghost = true := by
  refine ⟨TypedBorrowSteps.registeredFrame frame borrowFrame id global.nextPointerTag,
    (liveRetagState frames frame machine borrowFrame global fresh id entry parentTag capacity).machine,
    rfl, rfl, rfl, rfl⟩

theorem nonlive_poststate
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (borrowFrame : FrameState) (global : GlobalState)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (localId : Miri.MIR.LocalId) :
    ∃ afterFrame afterMachine,
      nonliveRetagState frames frame machine borrowFrame global fresh id =
        Storage.withCurrent frames afterFrame afterMachine ∧
      afterFrame.locals = frame.locals ∧
      LocalPlaces.localRuntimePlace frames.size frame localId reference =
        LocalPlaces.localRuntimePlace frames.size afterFrame localId reference ∧
      afterMachine.user.payload.ghost = true := by
  refine ⟨TypedBorrowSteps.registeredFrame frame borrowFrame id global.nextPointerTag,
    (nonliveRetagState frames frame machine borrowFrame global fresh id).machine,
    rfl, rfl, rfl, rfl⟩

#print axioms validate_live
end
end DuplicatePrefix.ActualConcreteEmptyReference
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.ActualConcreteEmptyReference.live_poststate,
      ``DuplicatePrefix.ActualConcreteEmptyReference.nonlive_poststate,``DuplicatePrefix.ActualConcreteEmptyReference.validate_runtime_live,
      ``DuplicatePrefix.ActualConcreteEmptyReference.validate_runtime_nonlive,``DuplicatePrefix.ActualConcreteEmptyReference.validate_live,
      ``DuplicatePrefix.ActualConcreteEmptyReference.validate_nonlive] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved concrete empty dependency {dependency}"
