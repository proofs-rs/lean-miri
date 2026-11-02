import duplicate_prefix.PositiveGlobalFnEntryInput
import duplicate_prefix.GlobalEmptyReferenceReborrow
import duplicate_prefix.GeneralBorrowRawFnEntryExecution
import duplicate_prefix.StaticGlobalAllocInfo
import duplicate_prefix.GeneralBorrowFreshReborrowStages
import duplicate_prefix.DuplicatePrefixTypeCacheOrigins

namespace DuplicatePrefix.PositiveGlobalTypedReborrow
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter
open Miri.TreeBorrows Miri.DataStructures
open CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata TypedBorrowSteps TypedRetagEntry
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
-- Shared source-driver rewrite lists intentionally cover several branch shapes.
set_option linter.unusedSimpArgs false

/- Reuse the exact private source-driver proof steps, as the existing empty
materialization driver does. Name lookup is checked at elaboration time. -/
open Lean Elab in
elab "positive_global_rule " suffix:str : term => do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix.getString then some name else none
  let [name] := names | throwError "expected one original positive global proof step"
  Lean.Meta.mkConstWithFreshMVarLevels name

private theorem check_known {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (access : ValidityMachine.Access K U) (state : ValidityMachine.State K U)
    (id : AllocId) (tag : BorTag) (base offset len : UInt64) (info : AllocationInfo)
    (wiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (metadata : state.machine.memory.getAllocInfo id = .ok info)
    (kind : info.kind = .liveData)
    (positive : 0 < len.toNat) (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat + len.toNat ≤ info.size.bytes.toNat) :
    ValidityMachine.checkPointerAccess access
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base+offset))) (Size.ofBytes len) state =
      .ok () state := by
  have signed := DuplicatePrefix.signed_size_ok (Size.ofBytes len) signedFits
  change sizeAsI64 (Size.ofBytes len) = .ok (Int.ofNat len.toNat) at signed
  have resolved := MemoryCopyBridge.typed_resolve_cached pointers state.machine.memory state.machine
    id tag base offset (Int.ofNat len.toNat) width
    (by change -(2^63 : Int) ≤ (len.toNat : Int); omega)
    (by change (len.toNat : Int) < (2^63 : Int); omega) cached
  have resolveStep := (positive_global_rule ".RetagPointerChecks.validity_resolve_of_exact") access state
    (Pointer.new (some (Provenance.concrete id tag)) (Size.ofBytes (base+offset)))
    (Int.ofNat len.toNat) ⟨id,Size.ofBytes offset,.concrete tag⟩ (by rw [wiring]; exact resolved)
  have dereferenced := PointerAccess.dereference_ok ⟨access.runtime.pointerSize⟩
    (Pointer.new (some (Provenance.concrete id tag)) (Size.ofBytes (base+offset))) len.toNat
    (.dereferenceable "pointer") (fun _ _ => .ok ⟨id,Size.ofBytes offset,ProvenanceExtra.concrete tag⟩)
    state.machine.memory.getAllocInfo ⟨id,Size.ofBytes offset,ProvenanceExtra.concrete tag⟩ info
    positive signedFits rfl metadata (by simp [kind]) bounds
  have checked := (positive_global_rule ".RetagPointerChecks.pure_check_stage")
    ⟨access.runtime.pointerSize⟩ _ _ _ _ _ _ _ signed dereferenced
  have nonzero : (Int.ofNat len.toNat == 0) = false := by simp; omega
  exact (positive_global_rule ".RetagPointerChecks.check_pointer_stage")
    access state _ _ _ _ signed nonzero resolveStep checked

/-- The exact parent Read and newChild outcomes for the actual new root. The
proof-local cursor equals the already selected tag because raw FnEntry allocates
it internally; only the resulting identical protected set/tree steps are used.
No machine state is replaced by this proof-local global. -/
private theorem read_child (root tag : BorTag) (capacity offset len : UInt64)
    (protections : ProtectedTags) (positive : 0 < len.toNat)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat)
    (rootBelow : root.value.toNat < tag.value.toNat)
    (protectorBelow : ∀ row ∈ protections.entries, row.1.value.toNat < tag.value.toNat)
    (room : tag.value < 18446744073709551615) :
    let tree := BorrowTree.new root (Size.ofBytes capacity)
    let read := tree.performBorrowAccessRange (.concrete root) (Size.ofBytes offset) (Size.ofBytes len)
      .Read (protections.insert tag .StrongProtector) .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes offset) (.concrete root) tag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    read.status = .Completed ∧ child.outcome = .ok () := by
  let global := {GlobalState.new with protectedTags := protections, nextPointerTag := tag}
  have nonzero : capacity ≠ 0 := by intro zero; rw [zero] at bounds; simp only [UInt64.toNat_zero] at bounds; omega
  have runtime := PositiveGlobalFnEntryInput.new_runtime root capacity nonzero global rootBelow protectorBelow
  let input := PositiveGlobalFnEntryInput.new_input root capacity offset len global positive bounds room
  exact GeneralBorrowRawFnEntryExecution.completed _ global {} ⟨1, by decide⟩ runtime input

def finalTree (root tag : BorTag) (size : Size) (protections : ProtectedTags) (offset len : UInt64) :=
  let read := (BorrowTree.new root size).performBorrowAccessRange (.concrete root)
    (Size.ofBytes offset) (Size.ofBytes len) .Read protections .VisitChildrenOfAccessed
  (read.tree.newChild (Size.ofBytes offset) (.concrete root) tag
    (DedupRangeMap.new (Size.ofBytes len) ChildBorrow.fnEntryLocation) (.ReservedFrz false) true).tree

def completed (options : EvalConfigurationCore.Options) (state : RootState)
    (id : AllocId) (root tag : BorTag) (source : Allocation CtfeProvenance Unit)
    (converted : Allocation Provenance Unit) (protections : ProtectedTags) (offset len : UInt64) : RootState :=
  let cached := GlobalEmptyReferenceReborrow.materialized options state id root source converted
  {cached with machine := {cached.machine with memory := (RetagEntry.updatedMemory cached.machine.memory id
    ⟨.machine .global, converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)⟩
    (finalTree root tag source.byteSize protections offset len))}}

/-- Actual positive TypedRetag.reborrow from the ORIGINAL lazy-global prestate.
Pointer checking uses the original compiler metadata, then the real source
registers protection, materializes MEMORY/STATIC, performs the parent Read and
installs the protected child. No initial live row or successful operation is a
premise. The incoming concrete provenance is exactly the cached global root.

The explicit tag is the already allocated tag supplied to reborrow. Its raw
high-water/capacity resources suffice even when the existing root is protected.
Full typed pointer-value reconstruction and enclosing MIR calls are separate. -/
theorem reborrow (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (actualPointers : ctx.pointers = GlobalDataOnlyActualConfig.pointers PreparedReflection.actual.compiler
      PreparedReflection.actual.image (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions) ())
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (id : AllocId) (root tag : BorTag) (base offset len : UInt64)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (rootCached : tracker.global.rootTag? id = some root)
    (source : Allocation CtfeProvenance Unit)
    (supported : GlobalSupportedImage.Supported source PreparedReflection.actual.compiler.runtime.target
      machine.memory tracker.global.rootPointerTags machine.user.addresses.baseAddr)
    (race : machine.dataRace = none)
    (noExtras : (machine.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id)) = false)
    (absent : machine.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : machine.memory.hasFunctionPointer id = false) (noVaList : machine.memory.hasVaListId id = false)
    (descriptor : DuplicatePrefixEmptyReferenceInput.ImageDescriptor
      (DuplicatePrefixCallSpecification.imageContext options machine tracker) machine.memory id source)
    (window : DuplicatePrefixSliceStorage.Positive source.initializationMask source.byteSize.bytes offset len)
    (storage : source.len = source.byteSize.bytes.toNat) (mutable : source.mutability = .Mut)
    (rootBelow : root.value.toNat < tag.value.toNat)
    (protectorBelow : ∀ row ∈ tracker.global.protectedTags.entries, row.1.value.toNat < tag.value.toNat)
    (tagRoom : tag.value < 18446744073709551615) :
    let h := adapted options remaining span ctx.pointers
    let place := RetagReferencePlace.slicePlace
      (Pointer.new (.concrete id root) (Size.ofBytes (base+offset))) len pointee
    ∃ converted : Allocation Provenance Unit,
      GlobalAllocationAttributes.Attributes source converted ∧
      TypedRetag.reborrow h options.limits.retag place (Size.ofBytes len) ChildBorrow.fnEntryPolicy tag
        (Storage.withCurrent frames frame machine) =
        .ok (some (.concrete id tag))
          (completed options (registeredState frames frame borrowFrame machine tracker id tag)
            id root tag source converted (registeredGlobal tracker tag).protectedTags offset len) := by
  let h := adapted options remaining span ctx.pointers
  let place := RetagReferencePlace.slicePlace
    (Pointer.new (.concrete id root) (Size.ofBytes (base+offset))) len pointee
  let start := Storage.withCurrent frames frame machine
  let registered := registeredState frames frame borrowFrame machine tracker id tag
  have info : machine.memory.getAllocInfo id =
      .ok ⟨source.byteSize, source.align, .liveData, source.mutability⟩ := by
    rcases descriptor with memoryDescriptor | ⟨definition, initializer, staticDescriptor⟩
    · exact GlobalDataOnlyMaterialize.alloc_info machine id source absent noFunction noVaList memoryDescriptor
    · exact StaticGlobalAllocInfo.alloc_info machine id source definition absent noFunction noVaList staticDescriptor
  obtain ⟨converted, attributes, ensure, present, afterWindow, afterStorage, afterMutable⟩ :=
    PositiveGlobalMaterialization.ensure_positive options () remaining span registered (registeredTracker tracker tag)
      id root source supported rfl rootCached race noExtras absent descriptor offset len window storage mutable
  have positive : (0 : UInt64) < len := by
    simpa only [UInt64.lt_iff_toNat_lt, UInt64.toNat_zero] using window.positive
  have check : h.checkPtrAccess place.mplace.ptr (Size.ofBytes len) start = .ok () start := by
    rw [ctx.source.check]
    exact check_known ctx.pointers (config options remaining span).access start id root base offset len _
      ctx.resolve ctx.arithmetic cachedAddress info rfl window.positive window.signedSize window.bounds
  have resolve : h.resolveAllocation place.mplace.ptr start =
      .ok (some ⟨id,Size.ofBytes offset,.concrete root⟩) start := by
    rw [ctx.source.resolve]
    exact RetagPointerChecks.resolve_allocation_cached ctx.pointers start id root base offset ctx.arithmetic cachedAddress
  have log : h.logCreation = (fun _ _ _ _ _ => pure ()) := ctx.source.log
  have queries := reference_queries options remaining span ctx.pointers
  have inside := TypedRetagPolicyFields.inside_for_policy h options.limits.retag place (Size.ofBytes len)
    ChildBorrow.fnEntryPolicy ChildBorrow.fnEntryLocation
    (ChildBorrow.mutable_fn_entry_initial_location true) ctx.source.precise queries.freeze
  have ensureWiring : h.ensureTreeExtra = (config options remaining span).retag.ensureTreeExtra := by
    rw [ctx.source.ensure, actualPointers, GlobalDataOnlyActualConfig.actual_ensure]
  refine ⟨converted, attributes, ?_⟩
  change TypedRetag.reborrow h options.limits.retag place (Size.ofBytes len) ChildBorrow.fnEntryPolicy tag start = _
  unfold TypedRetag.reborrow
  simp only [log, check, resolve, bind, EStateM.bind, pure, EStateM.pure, ChildBorrow.fnEntryPolicy]
  rw [current_frame_pushed start frames frame rfl]
  simp only [frameBorrow, bind, EStateM.bind, pure, EStateM.pure]
  unfold_typed ".TypedRetag.tracker"
  simp only [get, getThe, MonadStateOf.get, EStateM.get, start, Storage.withCurrent, enabled,
    bind, EStateM.bind, pure, EStateM.pure]
  simp only [GlobalState.addProtector, FrameState.addProtector, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, MachineHooks.setCurrentFrame,
    get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure,
    set, EStateM.set, Storage.withCurrent, Array.isEmpty_push, Array.pop_push,
    Bool.false_eq_true, ↓reduceIte]
  unfold_typed ".TypedRetag.checked"
  simp only [info, bind, EStateM.bind, pure, EStateM.pure]
  have sameKind : (AllocationKind.liveData != .liveData) = false := rfl
  simp only [sameKind, Bool.false_eq_true, ↓reduceIte]
  erw [inside]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  rw [ensureWiring]
  erw [ensure]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  let cached := GlobalEmptyReferenceReborrow.materialized options registered id root source converted
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    ⟨.machine .global, converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)⟩
  let parentTree := (BorrowTree.new root source.byteSize).performBorrowAccessRange (.concrete root)
    (Size.ofBytes offset) (Size.ofBytes len) .Read (registeredGlobal tracker tag).protectedTags .VisitChildrenOfAccessed
  let child := parentTree.tree.newChild (Size.ofBytes offset) (.concrete root) tag
    (DedupRangeMap.new (Size.ofBytes len) ChildBorrow.fnEntryLocation) (.ReservedFrz false) true
  have stages := read_child root tag source.byteSize.bytes offset len tracker.global.protectedTags
    window.positive window.bounds rootBelow protectorBelow tagRoom
  have childExact : parentTree.tree.newChild (Size.ofBytes offset) (.concrete root) tag
      (DedupRangeMap.new (Size.ofBytes len) ChildBorrow.fnEntryLocation) ChildBorrow.fnEntryPolicy.outsidePermission
      ChildBorrow.fnEntryPolicy.protector.isSome = ⟨child.tree,.ok ()⟩ :=
    GeneralBorrowFreshReborrowStages.child_complete _ stages.2
  have result := (positive_global_rule ".TypedBorrowSteps.read_insert_steps") h frames
    (registeredFrame frame borrowFrame id tag) cached.machine (registeredTracker tracker tag) rfl id entry
    offset len (.concrete root) tag ChildBorrow.fnEntryLocation ChildBorrow.fnEntryPolicy rfl positive
    present race parentTree.tree child.tree rfl stages.1 childExact
  exact result

def resultState (options : EvalConfigurationCore.Options)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit)
    (converted : Allocation Provenance Unit) (offset len : UInt64) :=
  completed options
    (registeredState frames frame borrowFrame (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) id tracker.global.nextPointerTag)
    id root tracker.global.nextPointerTag source converted
    (registeredGlobal (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags offset len

/-- Fixed typed positive mutable-reference FnEntry from the original lazy-global
prestate, including tag allocation, metadata sizing, actual pointer resolution,
MEMORY/STATIC ensure, protected parent Read/child creation and reconstruction of
the returned concrete fat pointer. No initial live row, future borrow capability
or successful operation is assumed. Populated array caches are admitted through
raw Origins consistency, rather than a slice-ID-absence/empty-cache premise.

This local typed normalization endpoint is not a whole MIR call or a complete
ordinary-valid-input coverage theorem. Supported image metadata and global
high-water/resource/configuration facts retain their explicit scope. -/
theorem retag_pointer (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (actualPointers : ctx.pointers = GlobalDataOnlyActualConfig.pointers PreparedReflection.actual.compiler
      PreparedReflection.actual.image (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions) ())
    (cmp : ProjectionMetadataFacts.NullComparator) (dynamicFuel : Nat)
    (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (root : BorTag) (base offset len : UInt64)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (rootCached : tracker.global.rootTag? id = some root)
    (source : Allocation CtfeProvenance Unit)
    (supported : GlobalSupportedImage.Supported source PreparedReflection.actual.compiler.runtime.target
      machine.memory tracker.global.rootPointerTags machine.user.addresses.baseAddr)
    (race : machine.dataRace = none)
    (noExtras : (machine.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id)) = false)
    (absent : machine.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : machine.memory.hasFunctionPointer id = false) (noVaList : machine.memory.hasVaListId id = false)
    (descriptor : DuplicatePrefixEmptyReferenceInput.ImageDescriptor
      (DuplicatePrefixCallSpecification.imageContext options machine tracker) machine.memory id source)
    (window : DuplicatePrefixSliceStorage.Positive source.initializationMask source.byteSize.bytes offset len)
    (storage : source.len = source.byteSize.bytes.toNat) (mutable : source.mutability = .Mut)
    (rootBelow : root.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (protectorBelow : ∀ row ∈ tracker.global.protectedTags.entries,
      row.1.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins machine.user.payload.payload.user.types) :
    ∃ converted : Allocation Provenance Unit,
      GlobalAllocationAttributes.Attributes source converted ∧
      TypedRetag.retagPtrValue (adapted options remaining span ctx.pointers) options.limits.retag
        (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new (.concrete id root) (Size.ofBytes (base+offset))) len reference)
        reference.ty .FnEntry (Storage.withCurrent frames frame machine) =
        .ok (some (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len reference))
          (resultState options frames frame borrowFrame machine tracker fresh id root source converted offset len) := by
  let h := adapted options remaining span ctx.pointers
  let before := Storage.withCurrent frames frame machine
  let place := RetagReferencePlace.slicePlace
    (Pointer.new (.concrete id root) (Size.ofBytes (base+offset))) len pointee
  let oldPointer := Pointer.new (Provenance.concrete id root) (Size.ofBytes (base+offset))
  let newPointer := Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))
  let value := RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base oldPointer len reference
  let output := RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base newPointer len reference
  have queries := reference_queries options remaining span ctx.pointers
  have notConstructed := DuplicatePrefixTypeCacheOrigins.slice_not_constructed
    machine.user.payload.payload.user.types metadata origins
  have bounded : len ≤ 9223372036854775807 := by
    apply UInt64.le_iff_toNat_le.mpr
    change len.toNat ≤ 9223372036854775807
    have bound := window.signedSize
    omega
  have sizing : h.sizeAndAlign place before = .ok (some (Size.ofBytes len,Align.ONE)) before := by
    rw [←ctx.visitor.sizing]
    exact ProjectionMetadataFacts.actual_validity_size_at options remaining span cmp before dynamicFuel fuelEq len
      metadata notConstructed bounded place rfl rfl
  obtain ⟨converted, attributes, reborrowed⟩ := reborrow options remaining span ctx actualPointers
    frames frame borrowFrame frameBorrow (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
    (ReferenceBorrowDriver.allocatedTracker tracker fresh) rfl id root tracker.global.nextPointerTag base offset len
    cachedAddress rootCached source supported race noExtras absent noFunction noVaList descriptor window storage mutable
    rootBelow protectorBelow fresh
  refine ⟨converted, attributes, ?_⟩
  let after := resultState options frames frame borrowFrame machine tracker fresh id root source converted offset len
  have retagged := TypedBorrowSteps.retag_place_at_of_reborrow h options.limits.retag place ChildBorrow.fnEntryPolicy
    (Size.ofBytes len) Align.ONE before after tracker enabled fresh id (.concrete id root) rfl sizing reborrowed
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
    before after queries.shape queries.pointee_eq permission construct retagged reconstruct

end DuplicatePrefix.PositiveGlobalTypedReborrow
