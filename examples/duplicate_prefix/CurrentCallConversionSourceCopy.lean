import duplicate_prefix.CurrentCallConversionActualEnsure
import duplicate_prefix.CurrentCallTypedAfterEnsure
import duplicate_prefix.PositiveGlobalTypedReborrow
import duplicate_prefix.CurrentCallTypedSourceCopy

/-! Positive CURRENT source copying through the actual finite converter. The
saved q tag is allocated and registered before conversion; the actual changed
machine is retained. No initial Bool window or different-allocation assumption
is needed for this source-neutral frontend. -/
namespace DuplicatePrefix.CurrentCallConversionSourceCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata TypedBorrowSteps
open ReferenceBorrowDriver CurrentCallOrdinaryInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

abbrev rootEntry (root : BorTag) (converted : Allocation Provenance Unit) :
    LocalAllocation Provenance BorrowTree MiriMemoryKind :=
  ⟨.machine .global, converted.mapExtra (fun _ => BorrowTree.new root converted.byteSize)⟩

def rootMachine (options : EvalConfigurationCore.Options) (after : Before)
    (id : AllocId) (root : BorTag) (converted : Allocation Provenance Unit) : Before :=
  CurrentCallConversionMaterialize.installed
    (MemoryExtras.putAllocation (GlobalDataOnlyActualConfig.extras options) after id ⟨none, #[]⟩)
    id .global (rootEntry root converted).allocation

def childMachine (options : EvalConfigurationCore.Options) (after : Before)
    (id : AllocId) (root tag : BorTag) (converted : Allocation Provenance Unit)
    (held : ProtectedTags) (offset len : UInt64) : Before :=
  let initial := rootMachine options after id root converted
  {initial with memory := (RetagEntry.updatedMemory initial.memory id (rootEntry root converted)
    (PositiveGlobalTypedReborrow.finalTree root tag converted.byteSize held offset len))}

/-- Internal operation composition: the finite converter's actual equation is
used at the real registered phase, not assumed in ordinary-input validity. -/
theorem reborrow (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (actualPointers : ctx.pointers = GlobalDataOnlyActualConfig.pointers PreparedReflection.actual.compiler
      PreparedReflection.actual.image (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions) ())
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (machine : Before) (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (id : AllocId) (root tag : BorTag) (source : Allocation CtfeProvenance Unit)
    (base offset len : UInt64) (current : CurrentPayload machine id source)
    (absent : machine.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : machine.memory.hasFunctionPointer id = false) (noVaList : machine.memory.hasVaListId id = false)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (positive : 0 < len.toNat) (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat + len.toNat ≤ source.byteSize.bytes.toNat)
    (rootBelow : root.value.toNat < tag.value.toNat)
    (protectorBelow : ∀ row ∈ tracker.global.protectedTags.entries, row.1.value.toNat < tag.value.toNat)
    (tagRoom : tag.value < 18446744073709551615)
    (converted : Allocation Provenance Unit) (attributes : GlobalAllocationAttributes.Attributes source converted)
    (after : Before) (afterTracker : MachineHooks.BorrowState)
    (conversion : Allocation.adjustFromTcx source PreparedReflection.actual.compiler.runtime.target.base
      (fun _ _ state => .ok (AllocationCopy.snapshot source) state)
      (CurrentCallConversionActualEnsure.hooks options).rootPointer
      (registeredState frames frame borrowFrame machine tracker id tag).machine = .ok converted after)
    (afterEnabled : after.borrowTracker = some afterTracker)
    (afterRoot : afterTracker.global.rootTag? id = some root) (afterRace : after.dataRace = none)
    (afterExtras : (after.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id)) = false)
    (flags : afterTracker.global.protectedTags = (registeredGlobal tracker tag).protectedTags) :
    let h := adapted options remaining span ctx.pointers
    let place := RetagReferencePlace.slicePlace
      (Pointer.new (Provenance.concrete id root) (Size.ofBytes (base + offset))) len ProjectionMetadataFacts.sliceLayout
    TypedRetag.reborrow h options.limits.retag place (Size.ofBytes len) ChildBorrow.fnEntryPolicy tag
      (Storage.withCurrent frames frame machine) =
      .ok (some (.concrete id tag))
        (Storage.withCurrent frames (registeredFrame frame borrowFrame id tag)
          (childMachine options after id root tag converted (registeredGlobal tracker tag).protectedTags offset len)) := by
  let h := adapted options remaining span ctx.pointers
  let place := RetagReferencePlace.slicePlace
    (Pointer.new (Provenance.concrete id root) (Size.ofBytes (base + offset))) len ProjectionMetadataFacts.sliceLayout
  let start := Storage.withCurrent frames frame machine
  let registered := registeredState frames frame borrowFrame machine tracker id tag
  have info : machine.memory.getAllocInfo id = .ok ⟨source.byteSize, source.align, .liveData, source.mutability⟩ := by
    cases current with
    | memory descriptor => exact GlobalDataOnlyMaterialize.alloc_info machine id source absent noFunction noVaList descriptor
    | internalStatic definition descriptor row =>
      exact StaticGlobalAllocInfo.alloc_info machine id source definition absent noFunction noVaList descriptor
  have check : h.checkPtrAccess place.mplace.ptr (Size.ofBytes len) start = .ok () start := by
    rw [ctx.source.check]
    exact (positive_global_rule ".PositiveGlobalTypedReborrow.check_known") ctx.pointers (config options remaining span).access
      start id root base offset len _ ctx.resolve ctx.arithmetic cached info rfl positive signedFits bounds
  have resolve : h.resolveAllocation place.mplace.ptr start = .ok (some ⟨id, Size.ofBytes offset, .concrete root⟩) start := by
    rw [ctx.source.resolve]
    exact RetagPointerChecks.resolve_allocation_cached ctx.pointers start id root base offset ctx.arithmetic cached
  have queries := (positive_global_rule ".reference_queries") options remaining span ctx.pointers
  have inside := TypedRetagPolicyFields.inside_for_policy h options.limits.retag place (Size.ofBytes len)
    ChildBorrow.fnEntryPolicy ChildBorrow.fnEntryLocation
    (ChildBorrow.mutable_fn_entry_initial_location true) ctx.source.precise queries.freeze
  have ensureWiring : h.ensureTreeExtra = (config options remaining span).retag.ensureTreeExtra := by
    rw [ctx.source.ensure, actualPointers, GlobalDataOnlyActualConfig.actual_ensure]
  have registeredCurrent : CurrentPayload registered.machine id source := by
    cases current with
    | memory descriptor => exact .memory descriptor
    | internalStatic definition descriptor row => exact .internalStatic definition descriptor row
  have ensure := CurrentCallConversionActualEnsure.ensure options remaining span registered after afterTracker id root source converted
    registeredCurrent absent conversion afterEnabled afterRoot afterRace afterExtras
  have present : (rootMachine options after id root converted).memory.live.find? (fun row => row.1 == id) =
      some (id, rootEntry root converted) := MemoryCopyBridge.live_lookup_replaced _ _ _
  let parent := (BorrowTree.new root converted.byteSize).performBorrowAccessRange (.concrete root)
    (Size.ofBytes offset) (Size.ofBytes len) .Read afterTracker.global.protectedTags .VisitChildrenOfAccessed
  let child := parent.tree.newChild (Size.ofBytes offset) (.concrete root) tag
    (DedupRangeMap.new (Size.ofBytes len) ChildBorrow.fnEntryLocation) (.ReservedFrz false) true
  have stages := (positive_global_rule ".PositiveGlobalTypedReborrow.read_child") root tag
    source.byteSize.bytes offset len tracker.global.protectedTags positive bounds rootBelow protectorBelow tagRoom
  have readDone : parent.status = .Completed := by
    dsimp only [parent]
    rw [attributes.size, flags]
    exact stages.1
  have childDone : parent.tree.newChild (Size.ofBytes offset) (.concrete root) tag
      (DedupRangeMap.new (Size.ofBytes len) ChildBorrow.fnEntryLocation)
      ChildBorrow.fnEntryPolicy.outsidePermission ChildBorrow.fnEntryPolicy.protector.isSome = ⟨child.tree, .ok ()⟩ := by
    dsimp only [parent, child]
    rw [attributes.size, flags]
    exact GeneralBorrowFreshReborrowStages.child_complete _ stages.2
  have initialInfo : machine.memory.getAllocInfo id = .ok
      ⟨(rootEntry root converted).allocation.byteSize, (rootEntry root converted).allocation.align,
        .liveData, (rootEntry root converted).allocation.mutability⟩ := by
    change machine.memory.getAllocInfo id = .ok ⟨converted.byteSize, converted.align, .liveData, converted.mutability⟩
    rw [attributes.size, attributes.align, attributes.mutability]
    exact info
  have actual := CurrentCallTypedAfterEnsure.protected_reborrow h options.limits.retag place frames frame borrowFrame
    machine tracker enabled frameBorrow id (rootEntry root converted) offset len (.concrete root) tag
    ChildBorrow.fnEntryLocation ChildBorrow.fnEntryPolicy rfl rfl
    (by simpa only [UInt64.lt_iff_toNat_lt, UInt64.toNat_zero] using positive)
    check resolve (by rw [ctx.source.log]) inside initialInfo (rootMachine options after id root converted) afterTracker
    (by rw [ensureWiring]; exact ensure) afterEnabled present afterRace parent.tree child.tree rfl readDone childDone
  simpa only [childMachine, PositiveGlobalTypedReborrow.finalTree, parent, child, flags] using actual


/-- The original positive slice FnEntry pointer action through one actual
CURRENT conversion, retaining its actual post-machine. -/
theorem pointer (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (actualPointers : ctx.pointers = GlobalDataOnlyActualConfig.pointers PreparedReflection.actual.compiler
      PreparedReflection.actual.image (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions) ())
    (cmp : ProjectionMetadataFacts.NullComparator) (dynamicFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel + 1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (machine : Before) (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit)
    (base offset len : UInt64) (current : CurrentPayload machine id source)
    (absent : machine.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : machine.memory.hasFunctionPointer id = false) (noVaList : machine.memory.hasVaListId id = false)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (positive : 0 < len.toNat) (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat + len.toNat ≤ source.byteSize.bytes.toNat)
    (rootBelow : root.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (protectorBelow : ∀ row ∈ tracker.global.protectedTags.entries,
      row.1.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins machine.user.payload.payload.user.types)
    (converted : Allocation Provenance Unit) (attributes : GlobalAllocationAttributes.Attributes source converted)
    (after : Before) (afterTracker : MachineHooks.BorrowState)
    (conversion : Allocation.adjustFromTcx source PreparedReflection.actual.compiler.runtime.target.base
      (fun _ _ state => .ok (AllocationCopy.snapshot source) state)
      (CurrentCallConversionActualEnsure.hooks options).rootPointer
      (registeredState frames frame borrowFrame (allocatedMachine machine tracker fresh)
        (allocatedTracker tracker fresh) id tracker.global.nextPointerTag).machine = .ok converted after)
    (afterEnabled : after.borrowTracker = some afterTracker)
    (afterRoot : afterTracker.global.rootTag? id = some root) (afterRace : after.dataRace = none)
    (afterExtras : (after.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id)) = false)
    (flags : afterTracker.global.protectedTags =
      (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags) :
    TypedRetag.retagPtrValue (adapted options remaining span ctx.pointers) options.limits.retag
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (Provenance.concrete id root) (Size.ofBytes (base + offset))) len ActualReferenceMetadata.reference)
      ActualReferenceMetadata.reference.ty .FnEntry (Storage.withCurrent frames frame machine) =
      .ok (some (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base + offset))) len ActualReferenceMetadata.reference))
        (Storage.withCurrent frames (registeredFrame frame borrowFrame id tracker.global.nextPointerTag)
          (childMachine options after id root tracker.global.nextPointerTag converted afterTracker.global.protectedTags offset len)) := by
  let h := adapted options remaining span ctx.pointers
  let before := Storage.withCurrent frames frame machine
  let place := RetagReferencePlace.slicePlace
    (Pointer.new (Provenance.concrete id root) (Size.ofBytes (base+offset))) len pointee
  let oldPointer := Pointer.new (Provenance.concrete id root) (Size.ofBytes (base+offset))
  let newPointer := Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))
  let value := RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base oldPointer len reference
  let output := RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base newPointer len reference
  have queries := (positive_global_rule ".reference_queries") options remaining span ctx.pointers
  have notConstructed := DuplicatePrefixTypeCacheOrigins.slice_not_constructed
    machine.user.payload.payload.user.types metadata origins
  have bounded : len ≤ 9223372036854775807 := by
    apply UInt64.le_iff_toNat_le.mpr
    change len.toNat ≤ 9223372036854775807
    have bound := signedFits
    omega
  have sizing : h.sizeAndAlign place before = .ok (some (Size.ofBytes len,Align.ONE)) before := by
    rw [←ctx.visitor.sizing]
    exact ProjectionMetadataFacts.actual_validity_size_at options remaining span cmp before dynamicFuel fuelEq len
      metadata notConstructed bounded place rfl rfl
  have allocatedCurrent : CurrentPayload (allocatedMachine machine tracker fresh) id source := by
    cases current with
    | memory descriptor => exact .memory descriptor
    | internalStatic definition descriptor row => exact .internalStatic definition descriptor row
  have reborrowed := reborrow options remaining span ctx actualPointers frames frame borrowFrame frameBorrow
    (allocatedMachine machine tracker fresh) (allocatedTracker tracker fresh) rfl id root tracker.global.nextPointerTag
    source base offset len allocatedCurrent absent noFunction noVaList cached positive signedFits bounds rootBelow
    protectorBelow fresh converted attributes after afterTracker conversion afterEnabled afterRoot afterRace afterExtras flags
  let afterState := Storage.withCurrent frames (registeredFrame frame borrowFrame id tracker.global.nextPointerTag)
    (childMachine options after id root tracker.global.nextPointerTag converted afterTracker.global.protectedTags offset len)
  have reborrowedActual : TypedRetag.reborrow h options.limits.retag place (Size.ofBytes len) ChildBorrow.fnEntryPolicy
      tracker.global.nextPointerTag (TypedRetagEmpty.afterTag before tracker fresh) =
      .ok (some (.concrete id tracker.global.nextPointerTag)) afterState := by
    simpa only [afterState, flags, h, place, before, TypedRetagEmpty.afterTag, Storage.withCurrent, allocatedMachine, allocatedTracker] using reborrowed
  have retagged := TypedBorrowSteps.retag_place_at_of_reborrow h options.limits.retag place ChildBorrow.fnEntryPolicy
    (Size.ofBytes len) Align.ONE before afterState tracker enabled fresh id (.concrete id root) rfl sizing reborrowedActual
  have permission := TypedRetagPolicyFields.new_permission_general h pointee.ty .Mutable .FnEntry before frames frame rfl
    queries.unpin queries.unsafeUnpin queries.freeze ctx.source.implicitWrites
  have created : RetagPolicy.create ⟨true,true,true⟩ .Mutable .FnEntry ⟨false,false⟩ =
      some ChildBorrow.fnEntryPolicy := by decide
  rw [created] at permission
  have construct : h.immPtrToMPlace value = pure place := by
    rw [ctx.source.construct]
    exact RetagReferencePlace.canonical_from_immediate (config options remaining span).access
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts () oldPointer len reference pointee
      (by rw [reference_ty,pointee_ty]; exact RootMetadataQueries.mutable_slice_dereference)
      (by rw [pointee_ty]; exact pointee_layout) ProjectionMetadataFacts.slice_layout_shape.2.2
  have changed : TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag =
      RetagReferencePlace.slicePlace newPointer len pointee := rfl
  have reconstruct : h.reconstruct value (TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag) =
      pure output := by
    rw [ctx.source.reconstruct, changed]
    exact RetagReferencePlace.bound_reconstruct (config options remaining span).access h value newPointer len pointee
  exact TypedBorrowSteps.reference_pointer_of_steps h options.limits.retag value output place
    (TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag) pointee.ty .Mut .FnEntry ChildBorrow.fnEntryPolicy
    before afterState queries.shape queries.pointee_eq permission construct retagged reconstruct



private theorem validate_of_pointer (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (before : Before) (tracker : MachineHooks.BorrowState)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState)
    (id : AllocId) (root : BorTag) (base offset len : UInt64) (pointer : Pointer Provenance)
    (pointerEq : pointer = Pointer.new (Provenance.concrete id root) (Size.ofBytes (base + offset)))
    (cachedAddress : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (info : AllocationInfo) (known : before.memory.getAllocInfo id = .ok info) (kind : info.kind = .liveData)
    (positive : 0 < len.toNat) (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat + len.toNat ≤ info.size.bytes.toNat) (pointerNonzero : pointer.offset.bytes ≠ 0)
    (nullComparator : ProjectionMetadataFacts.NullComparator) (dynamicFuel validationFuel : Nat)
    (fuelEq : options.place.dynamicFuel = dynamicFuel + 1) (validationEq : options.limits.validation = validationFuel + 1)
    (metadata : before.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins before.user.payload.payload.user.types)
    (debugOff : options.place.debugAssertions = false) (ghostOff : before.user.payload.ghost = false)
    (shallowMode : before.user.payload.validation = .Shallow)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (CurrentCallTypedSourceCopy.value options remaining span pointer len).imm))
    (cached : frame.locals[localId].layout = some ActualReferenceMetadata.reference)
    (post : Before) (postGhost : post.user.payload.ghost = true)
    (typedEq : TypedRetag.retagPtrValue (adapted options remaining span ctx.pointers) options.limits.retag
      (CurrentCallTypedSourceCopy.value options remaining span pointer len) ActualReferenceMetadata.reference.ty .FnEntry
      (Storage.withCurrent frames frame (CurrentCallReferenceEntry.view before tracker .FnEntry true)) =
      .ok (some (CurrentCallTypedSourceCopy.value options remaining span
        (CurrentCallTypedFnEntry.changedPointer pointer id tracker.global.nextPointerTag) len))
        (Storage.withCurrent frames (registeredFrame frame borrowFrame id tracker.global.nextPointerTag) post)) :
    ValidityMachine.validateRuntime (config options remaining span).validity () options.limits.validation
      (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference) true
      (Storage.withCurrent frames frame (ScopedFrame.entered before tracker .FnEntry)) =
      .ok () (Storage.withCurrent frames
        (CurrentCallTypedSourceCopy.writtenFrame options remaining span frame borrowFrame localId valid pointer len id tracker.global.nextPointerTag)
        {post with user := {post.user with payload := {post.user.payload with ghost := false}}}) := by
  have notConstructed:=DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ metadata origins
  have bounded : len≤9223372036854775807 := by apply UInt64.le_iff_toNat_le.mpr;change len.toNat≤9223372036854775807;omega
  have sizingInput : (adapted options remaining span ctx.pointers).sizeAndAlign
      (RetagReferencePlace.slicePlace pointer len ProjectionMetadataFacts.sliceLayout)
      (Storage.withCurrent frames frame (CurrentCallReferenceEntry.view before tracker .FnEntry true)) =
      .ok (some (Size.ofBytes len,Align.ONE)) (Storage.withCurrent frames frame (CurrentCallReferenceEntry.view before tracker .FnEntry true)) := by
    rw [←ctx.visitor.sizing]
    exact ProjectionMetadataFacts.actual_validity_size_at options remaining span nullComparator (Storage.withCurrent frames frame (CurrentCallReferenceEntry.view before tracker .FnEntry true)) dynamicFuel fuelEq len metadata notConstructed bounded (RetagReferencePlace.slicePlace pointer len ProjectionMetadataFacts.sliceLayout) rfl rfl
  let cfg := config options remaining span
  let h := adapted options remaining span ctx.pointers
  let machine := ScopedFrame.entered before tracker .FnEntry
  let active := CurrentCallReferenceEntry.view before tracker .FnEntry true
  let state := Storage.withCurrent frames frame active
  let destination := LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference
  let value := RetagReferencePlace.sliceValue cfg.access.runtime.base pointer len ActualReferenceMetadata.reference
  let adjusted := RetagReferencePlace.sliceValue cfg.access.runtime.base
    (CurrentCallTypedFnEntry.changedPointer pointer id tracker.global.nextPointerTag) len ActualReferenceMetadata.reference
  let sourcePlace := RetagReferencePlace.slicePlace pointer len ProjectionMetadataFacts.sliceLayout
  let afterFrame := registeredFrame frame borrowFrame id tracker.global.nextPointerTag
  let afterMachine := post
  let written := Storage.withCurrent frames (CurrentCallTypedSourceCopy.writtenFrame options remaining span frame borrowFrame localId valid pointer len id tracker.global.nextPointerTag) afterMachine
  have liveValue := live
  have nonzero : pointer.offset.bytes ≠ 0 := pointerNonzero
  have unitCheck : ValidityMachine.checkPointerAccess cfg.access sourcePlace.mplace.ptr (Size.ofBytes len) state=.ok () state := by
    dsimp only [sourcePlace]
    rw [pointerEq]
    exact (positive_global_rule ".PositiveGlobalTypedReborrow.check_known") ctx.pointers cfg.access state id root base offset len _ ctx.resolve ctx.arithmetic cachedAddress
      known kind positive signedFits bounds
  have debug : ctx.inner.debugAssertions = false := ctx.innerDebug.trans
    ((CanonicalConfigFacts.actual_fields options () remaining span).debug.trans debugOff)
  have noDebug : ctx.inner.debugAbiCheck adjusted.imm ActualReferenceMetadata.reference = pure () := by
    rw [ctx.innerAbi,(CanonicalConfigFacts.actual_fields options () remaining span).debugAbiNoChecks debugOff]
  obtain ⟨pa,pb,ra,rb,pairOffset,repr⟩ := ActualReferenceMetadata.reference_repr
  obtain ⟨_,tail,inhabited,named,classified⟩ := ActualReferenceMetadata.visitor_metadata options remaining span
  have dereference : CompilerFacts.builtinDeref ReferenceMetadataFacts.prepared.context ActualReferenceMetadata.reference.ty true =
      .ok (some ProjectionMetadataFacts.sliceLayout.ty) := by
    rw [ActualReferenceMetadata.reference_ty,ProjectionMetadataFacts.slice_layout_shape.1]
    exact RootMetadataQueries.mutable_slice_dereference
  have read : cfg.validity.readImmediate () destination .reference state = .ok value state := by
    rw [ctx.visitor.read]
    exact ReferenceValidity.read_local_pair_ghost cfg.access cfg.allocation ctx.inner () frames frame active localId
      ActualReferenceMetadata.reference _ _ valid liveValue cached ActualReferenceMetadata.reference_sized debug rfl
      pa pb ra rb pairOffset repr (CanonicalConfigFacts.actual_retain_touched options () remaining span) .reference
  have construct : cfg.validity.ptrToPlace () value = pure sourcePlace := by
    rw [ctx.pointer]
    exact RetagReferencePlace.canonical_from_immediate cfg.access ReferenceMetadataFacts.prepared () pointer len
      ActualReferenceMetadata.reference ProjectionMetadataFacts.sliceLayout dereference ActualReferenceMetadata.pointee_layout
      ProjectionMetadataFacts.slice_layout_shape.2.2
  have metadata : source_check_metadata cfg.validity () sourcePlace = pure () :=
    ReferenceValidity.metadata_slice cfg.validity () sourcePlace len tail rfl
      (ActualReferenceMetadata.visitor_target options remaining span).2
  have sizing : cfg.validity.sizeAndAlign () sourcePlace state = .ok (some (Size.ofBytes len,Align.ONE)) state := by
    rw [ctx.visitor.sizing]
    exact sizingInput
  have checked : cfg.validity.checkPointerAccess () sourcePlace.mplace.ptr (Size.ofBytes len) state = .ok (.ok ()) state := by
    rw [ctx.visitor.check]
    exact (positive_global_rule ".CurrentCallTypedSourceCopy.check_result_of_unit") cfg.access sourcePlace.mplace.ptr (Size.ofBytes len) state unitCheck
  have retagged : cfg.validity.retagPointer () value ActualReferenceMetadata.reference.ty state =
      .ok (some adjusted) (Storage.withCurrent frames afterFrame afterMachine) := by
    rw [ctx.visitor.retagAction]
    unfold TypedRetag.machineRetagPtrValue
    simp only [state,active,CurrentCallReferenceEntry.view,ScopedFrame.entered,Storage.withCurrent,get,getThe,MonadStateOf.get,EStateM.get,
      bind,EStateM.bind]
    exact typedEq
  have write : cfg.validity.writeNoValidate () adjusted.imm destination
      (Storage.withCurrent frames afterFrame afterMachine) = .ok () written := by
    rw [ctx.visitor.write]
    exact ReferenceValidity.visitor_write_local_ghost cfg.access cfg.allocation ctx.inner () frames afterFrame afterMachine localId
      value.imm adjusted.imm ActualReferenceMetadata.reference valid liveValue cached ActualReferenceMetadata.reference_sized
      debug noDebug postGhost
  have encoded : Scalar.fromMaybePointer cfg.validity.target.base sourcePlace.mplace.ptr =
      .ok (Scalar.fromPointer cfg.validity.target.base pointer) := rfl
  have nonnull : cfg.validity.scalarMayBeNull () (Scalar.fromPointer cfg.validity.target.base pointer) = pure false := by
    rw [ctx.visitor.nonnull]
    exact ReferenceChecks.pointer_not_null cfg.validity.target.base pointer
      (ActualReferenceMetadata.visitor_target options remaining span).1 nonzero
  have aligned : cfg.validity.checkPointerAlignResult () sourcePlace.mplace.ptr Align.ONE written = .ok (.ok ()) written := by
    rw [ctx.visitor.align]
    exact ReferenceChecks.alignment_one cfg.access sourcePlace.mplace.ptr written
  have checkedReference := ReferenceValidity.check_reference_stage_for cfg.validity () "&mut [u8]" true destination value adjusted sourcePlace
    (Size.ofBytes len) Align.ONE _ state (Storage.withCurrent frames afterFrame afterMachine) written read construct
    ProjectionMetadataFacts.slice_layout_shape.2.1 metadata sizing checked retagged write encoded nonnull inhabited aligned
  have visited : ValidityVisitor.visit cfg.validity () (validationFuel+1) (ReferenceValidity.referenceSession "&mut [u8]") destination state =
      .ok (ReferenceValidity.referenceSession "&mut [u8]") written :=
    ReferenceValidity.visit_reference_of_check_for cfg.validity () validationFuel "&mut [u8]" true destination state written classified checkedReference
  have toOp : cfg.validity.toOp () destination state = .ok ⟨.immediate value.imm,ActualReferenceMetadata.reference⟩ state := by
    rw [ctx.visitor.toOp]
    exact ScalarCopyStage.place_to_op_ghost cfg.access cfg.allocation ctx.inner () frames frame active localId
      ActualReferenceMetadata.reference value.imm valid liveValue cached ActualReferenceMetadata.reference_sized debug rfl
  have shallow := ReferenceValidity.validate_reference_shallow_of_visit cfg.validity () validationFuel "&mut [u8]" destination
    (Storage.withCurrent frames frame machine) written value.imm ghostOff postGhost
    named ctx.visitor.ghost toOp visited
  have recursive : ValidityMachine.enforceValidityRecursively (Storage.withCurrent frames frame machine) =
      .ok false (Storage.withCurrent frames frame machine) := by
    simp [ValidityMachine.enforceValidityRecursively,Storage.withCurrent,machine,ScopedFrame.entered,shallowMode,
      get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
  rw [validationEq]
  change ValidityMachine.validateRuntime cfg.validity () (validationFuel+1) destination true (Storage.withCurrent frames frame machine) = _
  unfold ValidityMachine.validateRuntime
  simp only [bind,EStateM.bind,recursive]
  exact shallow


/-- Real source copy/validation in its one FnEntry scope. The internal converter
starts after the fresh q tag has been allocated and registered in the copied
frame. Its actual machine, address cache and choice tape are never reset. -/
theorem invoke (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : Context options remaining span)
    (actualPointers : ctx.pointers = GlobalDataOnlyActualConfig.pointers PreparedReflection.actual.compiler
      PreparedReflection.actual.image (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions) ())
    (before : Before) (tracker : MachineHooks.BorrowState) (enabled : before.borrowTracker = some tracker)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit) (base offset len : UInt64)
    (current : CurrentPayload before id source)
    (absent : before.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : before.memory.hasFunctionPointer id = false) (noVaList : before.memory.hasVaListId id = false)
    (cachedAddress : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (positive : 0 < len.toNat) (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat + len.toNat ≤ source.byteSize.bytes.toNat)
    (nonnull : base + offset ≠ 0)
    (rootBelow : root.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (protectorBelow : ∀ row ∈ tracker.global.protectedTags.entries,
      row.1.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (nullComparator : ProjectionMetadataFacts.NullComparator) (dynamicFuel validationFuel : Nat)
    (fuelEq : options.place.dynamicFuel = dynamicFuel + 1) (validationEq : options.limits.validation = validationFuel + 1)
    (metadata : before.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins before.user.payload.payload.user.types)
    (debugOff : options.place.debugAssertions = false) (ghostOff : before.user.payload.ghost = false)
    (shallowMode : before.user.payload.validation = .Shallow)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (old : Immediate Provenance) (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some ActualReferenceMetadata.reference) (noClocks : frame.extra.dataRace = none)
    (converted : Allocation Provenance Unit) (attributes : GlobalAllocationAttributes.Attributes source converted)
    (after : Before) (afterTracker : MachineHooks.BorrowState)
    (conversion :
      let ptr := Pointer.new (Provenance.concrete id root) (Size.ofBytes (base + offset))
      let copied := CurrentCallTypedSourceCopy.copiedFrame options remaining span frame localId valid ptr len
      let active := CurrentCallReferenceEntry.view before tracker .FnEntry true
      Allocation.adjustFromTcx source PreparedReflection.actual.compiler.runtime.target.base
        (fun _ _ state => .ok (AllocationCopy.snapshot source) state)
        (CurrentCallConversionActualEnsure.hooks options).rootPointer
        (registeredState frames copied borrowFrame (allocatedMachine active {tracker with retagMode := .FnEntry} room)
          (allocatedTracker {tracker with retagMode := .FnEntry} room) id tracker.global.nextPointerTag).machine = .ok converted after)
    (afterEnabled : after.borrowTracker = some afterTracker)
    (afterRoot : afterTracker.global.rootTag? id = some root) (afterRace : after.dataRace = none)
    (afterExtras : (after.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id)) = false)
    (afterGhost : after.user.payload.ghost = true)
    (flags : afterTracker.global.protectedTags =
      (registeredGlobal (allocatedTracker {tracker with retagMode := .FnEntry} room) tracker.global.nextPointerTag).protectedTags) :
    let ptr := Pointer.new (Provenance.concrete id root) (Size.ofBytes (base + offset))
    let copied := CurrentCallTypedSourceCopy.copiedFrame options remaining span frame localId valid ptr len
    let validCopied : localId < copied.locals.size := by simpa only [copied, CurrentCallTypedSourceCopy.copiedFrame, Array.size_set] using valid
    let doneFrame := CurrentCallTypedSourceCopy.writtenFrame options remaining span copied borrowFrame localId validCopied ptr len id tracker.global.nextPointerTag
    let raw := childMachine options after id root tracker.global.nextPointerTag converted afterTracker.global.protectedTags offset len
    let validated := {raw with user := {raw.user with payload := {raw.user.payload with ghost := false}}}
    let restored := {validated with borrowTracker := some {afterTracker with retagMode := tracker.retagMode}}
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyAllowTransmute ()
      ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span ptr len).imm, ActualReferenceMetadata.reference⟩
      (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView
      (Storage.withCurrent frames frame (ScopedFrame.entered before tracker .FnEntry)) =
        .ok () (Storage.withCurrent frames doneFrame validated) ∧
    MachineHooks.withRetagMode .FnEntry
      ((ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyAllowTransmute ()
        ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span ptr len).imm, ActualReferenceMetadata.reference⟩
        (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView)
      (Storage.withCurrent frames frame before) = .ok () (Storage.withCurrent frames doneFrame restored) ∧
    doneFrame.extra.borrowTracker = some (borrowFrame.addProtector id tracker.global.nextPointerTag) ∧
    doneFrame.locals.size = frame.locals.size := by
  let ptr := Pointer.new (Provenance.concrete id root) (Size.ofBytes (base + offset))
  let copied := CurrentCallTypedSourceCopy.copiedFrame options remaining span frame localId valid ptr len
  have validCopied : localId < copied.locals.size := by simpa only [copied, CurrentCallTypedSourceCopy.copiedFrame, Array.size_set] using valid
  have liveCopied : copied.locals[localId].value = .live (.immediate (CurrentCallTypedSourceCopy.value options remaining span ptr len).imm) := by
    simp only [copied, CurrentCallTypedSourceCopy.copiedFrame, Array.getElem_set_self]
  have cachedCopied : copied.locals[localId].layout = some ActualReferenceMetadata.reference := by
    simpa only [copied, CurrentCallTypedSourceCopy.copiedFrame, Array.getElem_set_self] using cached
  let active := CurrentCallReferenceEntry.view before tracker .FnEntry true
  have activeCurrent : CurrentPayload active id source := by
    cases current with
    | memory descriptor => exact .memory descriptor
    | internalStatic definition descriptor row => exact .internalStatic definition descriptor row
  have typed := pointer options remaining span ctx actualPointers nullComparator dynamicFuel fuelEq frames copied borrowFrame frameBorrow
    active {tracker with retagMode := .FnEntry} rfl room id root source base offset len activeCurrent absent noFunction noVaList
    cachedAddress positive signedFits bounds rootBelow protectorBelow metadata origins converted attributes after afterTracker conversion
    afterEnabled afterRoot afterRace afterExtras flags
  have adjusted : CurrentCallTypedFnEntry.changedPointer ptr id tracker.global.nextPointerTag =
      Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base + offset)) := rfl
  rw [← adjusted] at typed
  have info : before.memory.getAllocInfo id = .ok ⟨source.byteSize, source.align, .liveData, source.mutability⟩ := by
    cases current with
    | memory descriptor => exact GlobalDataOnlyMaterialize.alloc_info before id source absent noFunction noVaList descriptor
    | internalStatic definition descriptor row =>
      exact StaticGlobalAllocInfo.alloc_info before id source definition absent noFunction noVaList descriptor
  let raw := childMachine options after id root tracker.global.nextPointerTag converted afterTracker.global.protectedTags offset len
  have checked := validate_of_pointer options remaining span ctx before tracker frames copied borrowFrame id root base offset len ptr rfl
    cachedAddress _ info rfl positive signedFits bounds nonnull nullComparator dynamicFuel validationFuel fuelEq validationEq metadata origins
    debugOff ghostOff shallowMode localId validCopied liveCopied cachedCopied raw afterGhost typed
  let doneFrame := CurrentCallTypedSourceCopy.writtenFrame options remaining span copied borrowFrame localId validCopied ptr len id tracker.global.nextPointerTag
  let validated := {raw with user := {raw.user with payload := {raw.user.payload with ghost := false}}}
  let restored := {validated with borrowTracker := some {afterTracker with retagMode := tracker.retagMode}}
  have copiedAction := ReferenceArgumentCopy.copy_with_nested_validation options limits remaining span debugOff frames frame
    (ScopedFrame.entered before tracker .FnEntry) localId old (CurrentCallTypedSourceCopy.value options remaining span ptr len).imm
    valid live cached noClocks ghostOff shallowMode
    (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView (by simp)
    (Storage.withCurrent frames doneFrame validated) checked
  have tracked : validated.borrowTracker = some afterTracker := afterEnabled
  have scopedAction := ScopedFrame.changed_state _ (Storage.withCurrent frames frame before) (Storage.withCurrent frames doneFrame validated)
    tracker afterTracker .FnEntry () enabled tracked copiedAction
  exact ⟨copiedAction, scopedAction, rfl, by simp only [doneFrame, CurrentCallTypedSourceCopy.writtenFrame, copied, CurrentCallTypedSourceCopy.copiedFrame, Array.size_set]⟩

end DuplicatePrefix.CurrentCallConversionSourceCopy
