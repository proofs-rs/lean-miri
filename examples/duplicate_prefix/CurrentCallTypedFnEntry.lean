import duplicate_prefix.CurrentCallAdmission
import duplicate_prefix.GeneralBorrowRawWildcardWindowTypedFnEntry
import duplicate_prefix.ActualReferenceMetadata
import duplicate_prefix.CandidateCurrentWindowPointerChecks

/-! Actual positive mutable-u8 FnEntry retag from the proposed current-call
clauses. Interior pointer offsets and same-allocation Bool authority are kept.
The proposal remains unadopted; this is a conditional interpreter theorem. -/
namespace DuplicatePrefix.CurrentCallTypedFnEntry
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentFnEntryRaw
open GeneralBorrowFnEntryRegistration TypedBorrowSteps ReferenceBorrowDriver
open CanonicalConfigFacts ActualReferenceContext
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

abbrev parent := CandidateCurrentWindowPointerChecks.extraOf

def literal (tree : BorrowTree) (global : GlobalState) (borrowFrame : FrameState) (id : AllocId)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (provenance : Provenance) (offset len : UInt64) : GeneralBorrowForestFnEntry.Output :=
  let registration := registered global borrowFrame id room
  let accessed := tree.performBorrowAccessRange (parent provenance) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registration.1.protectedTags .VisitChildrenOfAccessed
  ⟨registration.1,registration.2,global.nextPointerTag,accessed,
    accessed.tree.newChild (Size.ofBytes offset) (parent provenance) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) ChildBorrow.fnEntryLocation) (.ReservedFrz false) true⟩

/-- Normalization of the operation already proved by the raw consumer. The
associated Read and child equations used by the typed interpreter are internal
consequences of this literal equality, not assumptions of typed success. -/
theorem literal_operation (tree : BorrowTree) (global : GlobalState) (borrowFrame : FrameState) (id : AllocId)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (provenance : Provenance) (offset len : UInt64) :
    CandidateCurrentFnEntryRaw.operation tree global borrowFrame id provenance offset len =
      .ok (literal tree global borrowFrame id room provenance offset len) := by
  cases provenance <;>
    simp only [CandidateCurrentFnEntryRaw.operation,GeneralBorrowForestFnEntry.operation,
      GeneralBorrowRawWildcardFnEntryRuntime.operation,TypedRetagEmpty.allocate_tag global room,
      Except.bind,Except.pure,bind,pure]
  all_goals rfl

def changedPointer (pointer : Pointer Provenance) (id : AllocId) (tag : BorTag) : Pointer Provenance :=
  Pointer.new (.concrete id tag) pointer.offset

def installed (before : Before) (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tree : BorrowTree) : Before :=
  {registeredMachine (allocatedMachine before tracker room) (allocatedTracker tracker room) tracker.global.nextPointerTag with
    memory := RetagEntry.updatedMemory before.memory id entry tree}

/-- The raw witnesses accompany the actual typed operation and its memory
installation. In particular raw.sourceOwned/raw.boolOwned refer to the SAME
output tree/global used here; no post-state authority is supplied by the caller. -/
structure Outcome (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : Context options remaining span) (before : Before) (tracker : MachineHooks.BorrowState)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState)
    (argument : DuplicatePrefixSliceArgument.Argument) (len : UInt64) (place : MPlaceTy Provenance)
    (call : CallLoans) (data : Identities) where
  raw : CandidateCurrentFnEntryRaw.Result before tracker borrowFrame argument len place call data
  entry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  sourceLive : before.memory.live.find? (fun row => row.1 == call.sourceId) = some (call.sourceId,entry)
  sourceAllocation : entry.allocation = raw.sourceAllocation
  room : tracker.global.nextPointerTag.value < 18446744073709551615
  outputGlobal : raw.output.global = (registered tracker.global borrowFrame call.sourceId room).1
  outputFrame : (registeredFrame frame borrowFrame call.sourceId tracker.global.nextPointerTag).extra.borrowTracker =
    some raw.output.frame
  installedTracker : (installed before tracker room call.sourceId entry raw.output.child.tree).borrowTracker =
    some ⟨raw.output.global,tracker.retagMode⟩
  cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins
    (installed before tracker room call.sourceId entry raw.output.child.tree).user.payload.payload.user.types
  typed :
    TypedRetag.retagPtrValue (adapted options remaining span ctx.pointers) options.limits.retag
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base raw.sourcePointer.value len
        ActualReferenceMetadata.reference) ActualReferenceMetadata.reference.ty .FnEntry
      (Storage.withCurrent frames frame before) =
      .ok (some (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (changedPointer raw.sourcePointer.value call.sourceId tracker.global.nextPointerTag) len ActualReferenceMetadata.reference))
        (Storage.withCurrent frames (registeredFrame frame borrowFrame call.sourceId tracker.global.nextPointerTag)
          (installed before tracker room call.sourceId entry raw.output.child.tree))
  sourceInstalled :
    (installed before tracker room call.sourceId entry raw.output.child.tree).memory.live.find?
      (fun row => row.1 == call.sourceId) =
      some (call.sourceId,{entry with allocation := entry.allocation.setExtra raw.output.child.tree})

  boolInstalled : ∃ boolEntry,
    (installed before tracker room call.sourceId entry raw.output.child.tree).memory.live.find?
      (fun row => row.1 == call.returnId) = some (call.returnId,boolEntry) ∧
    boolEntry.allocation.extra = (if call.sourceId = call.returnId then raw.output.child.tree else raw.returnAllocation.extra)

/-- Fixed-metadata typed FnEntry with a newly supplied callee frame. The current
proposal chooses the raw source/Bool witness; pointer checks, resolution,
associated Read, child construction, policy queries and sizing are all derived. -/
theorem with_context (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (before : Before) (tracker : MachineHooks.BorrowState) (argument : DuplicatePrefixSliceArgument.Argument)
    (len : UInt64) (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (positive : 0 < len.toNat) :
    Nonempty (Outcome options remaining span ctx before tracker frames frame borrowFrame argument len place call data) := by
  obtain ⟨raw⟩ := input.positive_fnentry borrowFrame positive
  let cfg := config options remaining span
  let h := adapted options remaining span ctx.pointers
  let sourcePlace := RetagReferencePlace.slicePlace raw.sourcePointer.value len ProjectionMetadataFacts.sliceLayout
  let start := Storage.withCurrent frames frame before
  have room := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker len input.machine.resources
  have binding : CandidateCallBindings.WindowBinding before raw.sourcePointer.value call.sourceId call.sourceOffset len.toNat := by
    rcases input.actual.sourceAddress with empty | ⟨_,bits,argumentEq,loan,pointer,loanAt,pointerAt,valueEq,_,window⟩
    · simp [empty.1] at positive
    have bitsEq : bits = raw.sourcePointer.value := DuplicatePrefixSliceArgument.Argument.pointer.inj (argumentEq.symm.trans raw.argument_eq)
    rw [bitsEq,input.actual.length] at window
    exact window
  obtain ⟨entry,base,sourceLive,cachedAddress,byteLength,addressFits,sourceBounds,addressEq,nonnull,provenance⟩ := binding
  have sourcePresent : Present (ActualWorld before) call.sourceId entry.allocation := by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(call.sourceId,entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some sourceLive),rfl⟩
  have allocationEq := CandidateCurrentUniformOwnerWindow.same_id (ActualWorld before).toList input.machine.worldIds
    call.sourceId entry.allocation raw.sourceAllocation sourcePresent raw.sourcePresent
  have signedFits : len.toNat < 9223372036854775808 := by
    rcases input.actual.sourceValue with ⟨zero,_⟩ | ⟨_,allocation,_,physical⟩
    · simp [zero] at positive
    · exact physical.signedSize
  let allocated := allocatedMachine before tracker room
  let allocatedBorrow := allocatedTracker tracker room
  have allocatedBinding : CandidateCallBindings.WindowBinding allocated raw.sourcePointer.value call.sourceId call.sourceOffset len.toNat := by
    exact ⟨entry,base,sourceLive,cachedAddress,byteLength,addressFits,sourceBounds,addressEq,nonnull,provenance⟩
  obtain ⟨check,resolve⟩ := CandidateCurrentWindowPointerChecks.actual options remaining span ctx
    (Storage.withCurrent frames frame allocated) raw.sourcePointer.value call.sourceId call.sourceOffset len allocatedBinding positive signedFits
  have rawEq : raw.output = literal entry.allocation.extra tracker.global borrowFrame call.sourceId room
      raw.sourcePointer.value.provenance (UInt64.ofNat call.sourceOffset) len := by
    apply Except.ok.inj
    exact raw.actual.symm.trans (by rw [allocationEq];exact literal_operation _ _ _ _ room _ _ _)
  have queries := ActualReferenceMetadata.reference_queries options remaining span ctx.pointers
  have bounded : len ≤ 9223372036854775807 := by
    apply UInt64.le_iff_toNat_le.mpr
    change len.toNat ≤ 9223372036854775807
    omega
  have fuelPositive : 0 < options.place.dynamicFuel := by
    have budget := input.machine.resources.dynamicFuel
    unfold DuplicatePrefixCallSpecification.work at budget
    omega
  obtain ⟨dynamicFuel,fuelEq⟩ : ∃ fuel, options.place.dynamicFuel = fuel+1 := ⟨options.place.dynamicFuel-1,by omega⟩
  have metadata : (EvalProjectionMachine.arrays.get start).metadata = PreparedReflection.actual.runtime := input.machine.settings.metadata
  have origins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get start) := input.machine.cacheOrigins
  have notConstructed := DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ metadata origins
  have sizing : h.sizeAndAlign sourcePlace start = .ok (some (Size.ofBytes len,Align.ONE)) start := by
    rw [←ctx.visitor.sizing]
    exact ProjectionMetadataFacts.actual_validity_size_at options remaining span input.machine.settings.nullComparator start
      dynamicFuel fuelEq len metadata notConstructed bounded sourcePlace rfl rfl
  have inside := TypedRetagPolicyFields.inside_for_policy h options.limits.retag sourcePlace (Size.ofBytes len)
    ChildBorrow.fnEntryPolicy ChildBorrow.fnEntryLocation (ChildBorrow.mutable_fn_entry_initial_location true)
    ctx.source.precise queries.freeze
  have readDone := raw.readCompleted
  have childDone := raw.childCompleted
  rw [rawEq] at readDone childDone
  let accessed := entry.allocation.extra.performBorrowAccessRange (parent raw.sourcePointer.value.provenance)
    (Size.ofBytes (UInt64.ofNat call.sourceOffset)) (Size.ofBytes len) .Read
    (registered tracker.global borrowFrame call.sourceId room).1.protectedTags .VisitChildrenOfAccessed
  have childEq : accessed.tree.newChild (Size.ofBytes (UInt64.ofNat call.sourceOffset)) (parent raw.sourcePointer.value.provenance)
      tracker.global.nextPointerTag (DedupRangeMap.new (Size.ofBytes len) ChildBorrow.fnEntryLocation)
      ChildBorrow.fnEntryPolicy.outsidePermission ChildBorrow.fnEntryPolicy.protector.isSome = ⟨raw.output.child.tree,.ok ()⟩ := by
    rw [rawEq]
    change (literal _ _ _ _ _ _ _ _).child = ⟨(literal _ _ _ _ _ _ _ _).child.tree,.ok ()⟩
    cases found : (literal entry.allocation.extra tracker.global borrowFrame call.sourceId room raw.sourcePointer.value.provenance
        (UInt64.ofNat call.sourceOffset) len).child with
    | mk final outcome =>
      rw [found] at childDone
      cases childDone
      rfl
  have reborrow := protected_reborrow_of_steps h options.limits.retag sourcePlace frames frame borrowFrame allocated allocatedBorrow
    rfl frameBorrow call.sourceId entry (UInt64.ofNat call.sourceOffset) len (parent raw.sourcePointer.value.provenance)
    tracker.global.nextPointerTag ChildBorrow.fnEntryLocation ChildBorrow.fnEntryPolicy rfl rfl
    (by exact UInt64.lt_iff_toNat_lt.mpr positive)
    (by rw [ctx.source.check];exact check) (by rw [ctx.source.resolve];exact resolve)
    (by rw [ctx.source.log]) inside ctx.globalKind ctx.globals (ctx.source.ensure.trans ctx.ensure) ctx.synchronize
    sourceLive input.machine.settings.noDataRace accessed.tree raw.output.child.tree rfl
    (by simpa only [literal,accessed,registered,GeneralBorrowFnEntryRegistration.advanced,allocatedBorrow,allocatedTracker,
      registeredGlobal,GlobalState.addProtector,ite_true] using readDone) childEq
  have retag := retag_place_at_of_reborrow h options.limits.retag sourcePlace ChildBorrow.fnEntryPolicy (Size.ofBytes len) Align.ONE
    start (Storage.withCurrent frames (registeredFrame frame borrowFrame call.sourceId tracker.global.nextPointerTag)
      (installed before tracker room call.sourceId entry raw.output.child.tree)) tracker input.machine.state.enabled room
    call.sourceId raw.sourcePointer.value.provenance rfl sizing reborrow
  let changed := changedPointer raw.sourcePointer.value call.sourceId tracker.global.nextPointerTag
  let value := RetagReferencePlace.sliceValue cfg.access.runtime.base raw.sourcePointer.value len ActualReferenceMetadata.reference
  let output := RetagReferencePlace.sliceValue cfg.access.runtime.base changed len ActualReferenceMetadata.reference
  have permission := TypedRetagPolicyFields.new_permission_general h sourcePlace.layout.ty .Mutable .FnEntry start frames frame rfl
    queries.unpin queries.unsafeUnpin queries.freeze ctx.source.implicitWrites
  have created : RetagPolicy.create ⟨true,true,true⟩ .Mutable .FnEntry ⟨false,false⟩ = some ChildBorrow.fnEntryPolicy := rfl
  rw [created] at permission
  have dereference : CompilerFacts.builtinDeref ReferenceMetadataFacts.prepared.context ActualReferenceMetadata.reference.ty true =
      .ok (some ProjectionMetadataFacts.sliceLayout.ty) := by
    rw [ActualReferenceMetadata.reference_ty,ProjectionMetadataFacts.slice_layout_shape.1]
    exact RootMetadataQueries.mutable_slice_dereference
  have construct : h.immPtrToMPlace value = pure sourcePlace := by
    rw [ctx.source.construct]
    exact RetagReferencePlace.canonical_from_immediate cfg.access ReferenceMetadataFacts.prepared () raw.sourcePointer.value len
      ActualReferenceMetadata.reference ProjectionMetadataFacts.sliceLayout dereference ActualReferenceMetadata.pointee_layout
      ProjectionMetadataFacts.slice_layout_shape.2.2
  have changedEq : TypedRetagGeneric.retaggedPlace sourcePlace call.sourceId tracker.global.nextPointerTag =
      RetagReferencePlace.slicePlace changed len ProjectionMetadataFacts.sliceLayout := rfl
  have reconstruct : h.reconstruct value (TypedRetagGeneric.retaggedPlace sourcePlace call.sourceId tracker.global.nextPointerTag) =
      pure output := by
    rw [ctx.source.reconstruct,changedEq]
    exact RetagReferencePlace.bound_reconstruct cfg.access h value changed len ProjectionMetadataFacts.sliceLayout
  have typed := reference_pointer_of_steps h options.limits.retag value output sourcePlace
    (TypedRetagGeneric.retaggedPlace sourcePlace call.sourceId tracker.global.nextPointerTag) ProjectionMetadataFacts.sliceLayout.ty
    .Mut .FnEntry ChildBorrow.fnEntryPolicy start
    (Storage.withCurrent frames (registeredFrame frame borrowFrame call.sourceId tracker.global.nextPointerTag)
      (installed before tracker room call.sourceId entry raw.output.child.tree))
    queries.shape queries.pointee_eq permission construct retag reconstruct
  have boolInstalled : ∃ boolEntry,
      (installed before tracker room call.sourceId entry raw.output.child.tree).memory.live.find?
        (fun row => row.1 == call.returnId) = some (call.returnId,boolEntry) ∧
      boolEntry.allocation.extra = (if call.sourceId = call.returnId then raw.output.child.tree else raw.returnAllocation.extra) := by
    by_cases same : call.sourceId = call.returnId
    · refine ⟨{entry with allocation := entry.allocation.setExtra raw.output.child.tree},?_,?_⟩
      · rw [←same]
        exact MemoryCopyBridge.live_lookup_replaced before.memory call.sourceId _
      · simp only [same,ite_true]
        rfl
    · obtain ⟨_,bits,placeEq,loan,pointer,loanAt,pointerAt,valueEq,_,window⟩ := input.actual.returnAddress
      have loanEq : loan = raw.returnLoan := Option.some.inj (loanAt.symm.trans raw.returnLoanAt)
      subst loan
      have pointerEq : pointer = raw.returnPointer := Option.some.inj (pointerAt.symm.trans raw.returnPointerAt)
      subst pointer
      rw [←valueEq] at window
      obtain ⟨returnEntry,_,returnLive,_,_,_,_,_,_,_⟩ := window
      have returnPresent : Present (ActualWorld before) call.returnId returnEntry.allocation := by
        simp only [Present,ActualWorld,Array.toList_map]
        exact List.mem_map.mpr ⟨(call.returnId,returnEntry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some returnLive),rfl⟩
      have returnEq := CandidateCurrentUniformOwnerWindow.same_id (ActualWorld before).toList input.machine.worldIds
        call.returnId returnEntry.allocation raw.returnAllocation returnPresent raw.returnPresent
      refine ⟨returnEntry,?_,?_⟩
      · change ((before.memory.live.filter fun row => row.1 != call.sourceId).push
          (call.sourceId,{entry with allocation := entry.allocation.setExtra raw.output.child.tree})).find?
            (fun row => row.1 == call.returnId) = _
        rw [Array.find?_push,Array.find?_filter]
        have predicate : (fun row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind =>
            decide ((row.1 != call.sourceId) = true ∧ (row.1 == call.returnId) = true)) =
            (fun row => row.1 == call.returnId) := by
          funext row
          by_cases hit : row.1 = call.returnId
          · simp [hit,Ne.symm same]
          · simp [hit]
        rw [predicate,returnLive]
        rfl
      · simp only [same,ite_false,returnEq]
  refine ⟨{
    raw := raw
    entry := entry
    sourceLive := sourceLive
    sourceAllocation := allocationEq
    room := room
    outputGlobal := ?_
    outputFrame := ?_
    installedTracker := ?_
    cacheOrigins := input.machine.cacheOrigins
    typed := typed
    sourceInstalled := ?_
    boolInstalled := boolInstalled
  }⟩
  · rw [rawEq]
    rfl
  · rw [rawEq]
    rfl
  · rw [rawEq]
    rfl
  · exact MemoryCopyBridge.live_lookup_replaced before.memory call.sourceId
      {entry with allocation := entry.allocation.setExtra raw.output.child.tree}

/-- The actual source dictionary is constructed from the fixed settings;
no typed operation success or future authority appears in the inputs. -/
theorem invoke (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState) (argument : DuplicatePrefixSliceArgument.Argument)
    (len : UInt64) (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (positive : 0 < len.toNat) :
    ∃ ctx : Context options remaining span,
      Nonempty (Outcome options remaining span ctx before tracker frames frame borrowFrame argument len place call data) := by
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span
    input.machine.settings.preciseOff input.machine.settings.implicitOff
  exact ⟨ctx,with_context options limits remaining span ctx before tracker argument len place call data input
    frames frame borrowFrame frameBorrow positive⟩

end
end DuplicatePrefix.CurrentCallTypedFnEntry

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallTypedFnEntry." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved actual current typed FnEntry dependency {dependency}"
