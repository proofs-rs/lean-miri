import duplicate_prefix.CurrentCallLazyCurrentDescriptor
import duplicate_prefix.CurrentCallResourceFnEntry

/-! Actual positive typed source retagging for the cached, mutable CURRENT
MEMORY descriptor branch. Function/va-list exclusion is explicit selected
representation data. Supported image conversion, root/address caches and
initial old-node high-water facts retain their existing bounded scope.
Function/vtable/typeId relocation targets, TLS/extern static resolution and
byte-fragment conversion are outside this proof, without classifying their
interpreter behavior. This is neither a whole call nor ordinary-input coverage. -/
namespace DuplicatePrefix.CurrentCallLazyTypedSource
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open ActualReferenceContext ActualReferenceMetadata TypedBorrowSteps
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

abbrev nextTracker (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value<18446744073709551615) :=
  TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker room) tracker.global.nextPointerTag

private theorem registered_fields {before tracker data owner id offset length mode}
    (B : UniformWindow before tracker data owner id offset length mode)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615) :
    let current:=CurrentCallResourceFnEntry.registered_window B runtime frame room
    current.pointer=B.pointer ∧current.allocation=B.allocation ∧current.precise=B.precise := by
  unfold CurrentCallResourceFnEntry.registered_window
  rcases GeneralBorrowFnEntryRegistrationRuntime.prepare B.allocation.extra tracker.global frame id room runtime with ⟨a,b,c,d,e,f⟩
  exact ⟨rfl,rfl,rfl⟩

private theorem issued_world {before tracker id allocation completion grant}
    (issued : SpatialDelegation before tracker id allocation completion grant)
    (post : Before) (present : Present (ActualWorld post) id allocation) :
    SpatialDelegation post tracker id allocation completion grant := by
  induction issued with
  | allocated cap => exact .allocated {cap with live:=present}
  | concrete _ path ih => exact .concrete ih path
  | @wildcard origin root originNode rootNode earlier position originRoot _ originAt exposed rootAt parentless older before earlierAt rootSlot path edge ih =>
    exact .wildcard originNode rootNode earlier position originRoot ih originAt exposed rootAt parentless older before earlierAt rootSlot path edge

/-- Materialization and the real source-only constructor install preserve each
old allocation's presence. The fresh source is absent in the initial heap. -/
private theorem old_present (options : EvalConfigurationCore.Options)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState)
    (machine : Before) (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit)
    (converted : Allocation Provenance Unit) (offset len : UInt64)
    (other : AllocId) (allocation : Allocation Provenance BorrowTree) (different : other≠id)
    (present : Present (ActualWorld machine) other allocation) :
    Present (ActualWorld (PositiveGlobalTypedReborrow.resultState options frames frame borrowFrame machine tracker room
      id root source converted offset len).machine) other allocation := by
  simp only [Present,ActualWorld,Array.toList_map] at present ⊢
  obtain ⟨row,member,equal⟩:=List.mem_map.mp present
  have rowId : row.1=other:=congrArg Prod.fst equal
  have notSource : (row.1!=id)=true:=by simp [rowId,different]
  apply List.mem_map.mpr
  refine ⟨row,?_,equal⟩
  apply Array.mem_toList_iff.mpr
  apply Array.mem_push_of_mem
  apply Array.mem_filter.mpr
  refine ⟨?_,notSource⟩
  apply Array.mem_push_of_mem
  apply Array.mem_filter.mpr
  exact ⟨Array.mem_toList_iff.mp member,notSource⟩

private theorem bool_after {machine tracker data owner boolId boolOffset}
    (B : UniformWindow machine tracker data owner boolId boolOffset 1 .ret)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (options : EvalConfigurationCore.Options) (frames : Array CompilerFrameContext.ActualFrame)
    (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit) (converted : Allocation Provenance Unit)
    (offset len : UInt64) (different : boolId≠id) :
    ∃ current : UniformWindow (PositiveGlobalTypedReborrow.resultState options frames frame borrowFrame machine tracker room
      id root source converted offset len).machine (nextTracker tracker room) data owner boolId boolOffset 1 .ret,
      current.pointer=B.pointer ∧current.allocation=B.allocation ∧current.precise=B.precise := by
  let current:=CurrentCallResourceFnEntry.registered_window B runtime borrowFrame room
  have fields:=registered_fields B runtime borrowFrame room
  let post:=(PositiveGlobalTypedReborrow.resultState options frames frame borrowFrame machine tracker room id root source converted offset len).machine
  have present : Present (ActualWorld post) boolId current.allocation := by
    rw [fields.2.1]
    exact old_present options frames frame borrowFrame machine tracker room id root source converted offset len boolId B.allocation different B.present
  have issued:=issued_world current.issued post present
  let after : UniformWindow post (nextTracker tracker room) data owner boolId boolOffset 1 .ret := {
    loan:=current.loan,pointer:=current.pointer,allocation:=current.allocation,precise:=current.precise,
    loanAt:=current.loanAt,pointerAt:=current.pointerAt,pointerId:=current.pointerId,present:=present,preciseAt:=current.preciseAt,
    binding:=current.binding,issued:=issued,parents:=current.parents,window:=current.window}
  exact ⟨after,fields.1,fields.2.1,fields.2.2⟩


private theorem post_binding (options : EvalConfigurationCore.Options)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState)
    (machine : Before) (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit)
    (base offset len : UInt64) (argument : Pointer Provenance)
    (ready : CurrentCallLazyCurrentDescriptor.Ready options (Storage.withCurrent frames frame machine) tracker id root source base offset len argument)
    (converted : Allocation Provenance Unit) (attributes : GlobalAllocationAttributes.Attributes source converted) :
    CandidateCallBindings.WindowBinding
      (PositiveGlobalTypedReborrow.resultState options frames frame borrowFrame machine tracker room id root source converted offset len).machine
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) id offset.toNat len.toNat := by
  let tree:=PositiveGlobalTypedReborrow.finalTree root tracker.global.nextPointerTag source.byteSize
    (TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker tracker room) tracker.global.nextPointerTag).protectedTags offset len
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind:=⟨.machine .global,converted.mapExtra (fun _=>tree)⟩
  have live : (PositiveGlobalTypedReborrow.resultState options frames frame borrowFrame machine tracker room id root source converted offset len).machine.memory.live.find?
      (fun row=>row.1==id)=some (id,entry):=MemoryCopyBridge.live_lookup_replaced _ _ _
  have offsetBound : offset.toNat≤source.len:=by have bound:=ready.window.bounds;rw [ready.storage];omega
  have sumFits : base.toNat+offset.toNat<2^64:=by have room:=ready.addressRoom;omega
  refine ⟨entry,base,live,ready.cached,?_,?_,?_,?_,ready.nonnull,rfl⟩
  · change converted.len=converted.byteSize.bytes.toNat
    rw [attributes.storage,attributes.size]
    exact ready.storage
  · change base.toNat+converted.len<2^64
    rw [attributes.storage]
    exact ready.addressRoom
  · change offset.toNat+len.toNat≤converted.len
    rw [attributes.storage,ready.storage]
    exact ready.window.bounds
  · change (base+offset).toNat=base.toNat+offset.toNat
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt sumFits]

/-- Actual typed positive source FnEntry from the ORIGINAL caller state. The
real ensure executes inside retagging; the result retains its exact converted
bytes/tree and the SAME current Bool resource in the actual final world.

Selected function/va-list exclusion expresses the real getAllocInfo precedence.
It is not inferred from a memory descriptor, nor claimed for arbitrary ordinary
inputs. Image forms not admitted by Ready.supported remain outside this proof. -/
theorem invoke (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (preciseOff : options.retag.preciseInteriorMut=false) (implicitOff : options.retag.implicitWrites=false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (machine : Before) (tracker : MachineHooks.BorrowState)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit)
    (base offset len : UInt64) (argument : Pointer Provenance)
    (ready : CurrentCallLazyCurrentDescriptor.Ready options (Storage.withCurrent frames frame machine) tracker id root source base offset len argument)
    (noFunction : machine.memory.hasFunctionPointer id=false) (noVaList : machine.memory.hasVaListId id=false)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (cmp : ProjectionMetadataFacts.NullComparator) (dynamicFuel : Nat) (fuelEq : options.place.dynamicFuel=dynamicFuel+1)
    (metadata : machine.user.payload.payload.user.types.metadata=PreparedReflection.actual.runtime)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins machine.user.payload.payload.user.types)
    {data sourceOwner boolOwner boolId boolOffset}
    (license : CurrentCallLazyCurrentDescriptor.License data id offset len sourceOwner boolOwner boolId boolOffset)
    (B : UniformWindow machine tracker data boolOwner boolId boolOffset 1 .ret)
    (boolRuntime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global) :
    ∃ converted : Allocation Provenance Unit,GlobalAllocationAttributes.Attributes source converted ∧
    let post:=PositiveGlobalTypedReborrow.resultState options frames frame borrowFrame machine tracker fresh id root source converted offset len
    let tree:=PositiveGlobalTypedReborrow.finalTree root tracker.global.nextPointerTag source.byteSize
      (TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags offset len
    (PreparedContracts.actualConfig options () remaining span).retag.ensureTreeExtra=
      (GlobalDataOnlyActualConfig.pointers PreparedReflection.actual.compiler PreparedReflection.actual.image
        (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions) ()).ensureTreeExtra ∧
    TypedRetag.retagPtrValue (adapted options remaining span
      (GlobalDataOnlyActualConfig.pointers PreparedReflection.actual.compiler PreparedReflection.actual.image
        (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions) ())) options.limits.retag
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base argument len reference)
      reference.ty .FnEntry (Storage.withCurrent frames frame machine)=
      .ok (some (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len reference)) post ∧
    post.machine.memory.live.find? (fun row=>row.1==id)=some (id,⟨.machine .global,converted.mapExtra (fun _=>tree)⟩) ∧
    CandidateCallBindings.WindowBinding post.machine
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) id offset.toNat len.toNat ∧
    post.machine.borrowTracker=some (nextTracker tracker fresh) ∧
    (∀ other,(nextTracker tracker fresh).global.rootTag? other=tracker.global.rootTag? other) ∧
    id≠boolId ∧ CandidateFreezeContentResources.Valid (CandidateFreezeContentResources.union license.contents data.interpretation.content) ∧
    (∃ current : UniformWindow post.machine (nextTracker tracker fresh) data boolOwner boolId boolOffset 1 .ret,
      current.pointer=B.pointer ∧current.allocation=B.allocation ∧current.precise=B.precise) := by
  obtain ⟨ctx,actualPointers⟩:=GlobalEmptyReferenceContext.exists_context options remaining span preciseOff implicitOff
  obtain ⟨converted,attributes,actual⟩:=PositiveGlobalTypedReborrow.retag_pointer options remaining span ctx actualPointers cmp dynamicFuel fuelEq
    frames frame borrowFrame frameBorrow machine tracker ready.enabled fresh id root base offset len ready.cached ready.rootCached
    source ready.supported ready.race ready.noExtras ready.absent noFunction noVaList (Or.inl ready.descriptor)
    ready.window ready.storage ready.mutable ready.rootBelow ready.protectors metadata origins
  have different : id≠boolId := by
    intro equal
    have present:=B.present
    simp only [Present,ActualWorld,Array.toList_map] at present
    obtain ⟨row,member,rowEq⟩:=List.mem_map.mp present
    have absent:=Array.find?_eq_none.mp ready.absent row (Array.mem_toList_iff.mp member)
    have rowId : row.1=boolId:=congrArg Prod.fst rowEq
    simp [rowId,equal] at absent
  refine ⟨converted,attributes,GlobalDataOnlyActualConfig.actual_ensure options () remaining span,?_,?_,?_,?_,?_,different,
    CandidateFreezeContentResources.union_valid _ _ license.composable,?_⟩
  · rw [ready.argument]
    rw [actualPointers] at actual
    exact actual
  · exact MemoryCopyBridge.live_lookup_replaced _ _ _
  · exact post_binding options frames frame borrowFrame machine tracker fresh id root source base offset len argument ready converted attributes
  · rfl
  · intro other
    rfl
  · exact bool_after B boolRuntime options frames frame borrowFrame fresh id root source converted offset len (Ne.symm different)

end
end DuplicatePrefix.CurrentCallLazyTypedSource
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallLazyTypedSource" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual lazy typed source dependency {dependency}"
