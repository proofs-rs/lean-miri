import duplicate_prefix.CurrentCallTypedFnEntry

namespace DuplicatePrefix.CurrentCallTypedSourceOperation
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentFnEntryRaw
open GeneralBorrowFnEntryRegistration TypedBorrowSteps ReferenceBorrowDriver
open CanonicalConfigFacts ActualReferenceContext CurrentCallTypedFnEntry
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- The fixed mutable-slice typed FnEntry action consumes actual lower Read and
constructor certificates, retaining the original pointer and interior offset.
No ownership or completion packet is an input to this interpreter seam. -/
theorem typed_of_operation
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : Context options remaining span) (before : Before) (tracker : MachineHooks.BorrowState)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (enabled : before.borrowTracker=some tracker)
    (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (pointer : Pointer Provenance) (id : AllocId) (offset : Nat) (len : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (sourceLive : before.memory.live.find? (fun row=>row.1==id)=some (id,entry))
    (binding : CandidateCallBindings.WindowBinding before pointer id offset len.toNat)
    (positive : 0<len.toNat) (signedFits : len.toNat<9223372036854775808)
    (room : tracker.global.nextPointerTag.value<18446744073709551615) (race : before.dataRace=none)
    (nullComparator : ProjectionMetadataFacts.NullComparator) (dynamicFuel : Nat)
    (fuelEq : options.place.dynamicFuel=dynamicFuel+1)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame before)).metadata=PreparedReflection.actual.runtime)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame before)))
    (output : GeneralBorrowForestFnEntry.Output)
    (actual : CandidateCurrentFnEntryRaw.operation entry.allocation.extra tracker.global borrowFrame id pointer.provenance
      (UInt64.ofNat offset) len=.ok output)
    (readCompleted : output.access.status=.Completed) (childCompleted : output.child.outcome=.ok ()) :
    TypedRetag.retagPtrValue (adapted options remaining span ctx.pointers) options.limits.retag
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base pointer len ActualReferenceMetadata.reference)
      ActualReferenceMetadata.reference.ty .FnEntry (Storage.withCurrent frames frame before) =
      .ok (some (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (changedPointer pointer id tracker.global.nextPointerTag) len ActualReferenceMetadata.reference))
        (Storage.withCurrent frames (registeredFrame frame borrowFrame id tracker.global.nextPointerTag)
          (installed before tracker room id entry output.child.tree)) ∧
    output.global=(registered tracker.global borrowFrame id room).1 ∧
    output.tag=tracker.global.nextPointerTag ∧
    (registeredFrame frame borrowFrame id tracker.global.nextPointerTag).extra.borrowTracker=some output.frame ∧
    (installed before tracker room id entry output.child.tree).borrowTracker=some ⟨output.global,tracker.retagMode⟩ ∧
    DuplicatePrefixTypeCacheOrigins.Origins (installed before tracker room id entry output.child.tree).user.payload.payload.user.types ∧
    (installed before tracker room id entry output.child.tree).memory.live.find? (fun row=>row.1==id)=
      some (id,{entry with allocation:=entry.allocation.setExtra output.child.tree}) ∧
    (installed before tracker room id entry output.child.tree).user=before.user ∧
    (installed before tracker room id entry output.child.tree).threads=before.threads ∧
    (installed before tracker room id entry output.child.tree).dataRace=before.dataRace := by
  let cfg := config options remaining span
  let h := adapted options remaining span ctx.pointers
  let sourcePlace := RetagReferencePlace.slicePlace pointer len ProjectionMetadataFacts.sliceLayout
  let start := Storage.withCurrent frames frame before
  let allocated := allocatedMachine before tracker room
  let allocatedBorrow := allocatedTracker tracker room
  have allocatedBinding : CandidateCallBindings.WindowBinding allocated pointer id offset len.toNat := binding
  obtain ⟨check,resolve⟩ := CandidateCurrentWindowPointerChecks.actual options remaining span ctx
    (Storage.withCurrent frames frame allocated) pointer id offset len allocatedBinding positive signedFits
  have literalEq : output=literal entry.allocation.extra tracker.global borrowFrame id room pointer.provenance (UInt64.ofNat offset) len := by
    apply Except.ok.inj
    exact actual.symm.trans (literal_operation _ _ _ _ room _ _ _)
  have queries := ActualReferenceMetadata.reference_queries options remaining span ctx.pointers
  have bounded : len ≤ 9223372036854775807 := by
    apply UInt64.le_iff_toNat_le.mpr
    change len.toNat ≤ 9223372036854775807
    omega
  have notConstructed := DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ metadata origins
  have sizing : h.sizeAndAlign sourcePlace start = .ok (some (Size.ofBytes len,Align.ONE)) start := by
    rw [←ctx.visitor.sizing]
    exact ProjectionMetadataFacts.actual_validity_size_at options remaining span nullComparator start
      dynamicFuel fuelEq len metadata notConstructed bounded sourcePlace rfl rfl
  have inside := TypedRetagPolicyFields.inside_for_policy h options.limits.retag sourcePlace (Size.ofBytes len)
    ChildBorrow.fnEntryPolicy ChildBorrow.fnEntryLocation (ChildBorrow.mutable_fn_entry_initial_location true)
    ctx.source.precise queries.freeze
  have readDone := readCompleted
  have childDone := childCompleted
  rw [literalEq] at readDone childDone
  let accessed := entry.allocation.extra.performBorrowAccessRange (parent pointer.provenance)
    (Size.ofBytes (UInt64.ofNat offset)) (Size.ofBytes len) .Read
    (registered tracker.global borrowFrame id room).1.protectedTags .VisitChildrenOfAccessed
  have childEq : accessed.tree.newChild (Size.ofBytes (UInt64.ofNat offset)) (parent pointer.provenance)
      tracker.global.nextPointerTag (DedupRangeMap.new (Size.ofBytes len) ChildBorrow.fnEntryLocation)
      ChildBorrow.fnEntryPolicy.outsidePermission ChildBorrow.fnEntryPolicy.protector.isSome = ⟨output.child.tree,.ok ()⟩ := by
    rw [literalEq]
    change (literal _ _ _ _ _ _ _ _).child = ⟨(literal _ _ _ _ _ _ _ _).child.tree,.ok ()⟩
    cases found : (literal entry.allocation.extra tracker.global borrowFrame id room pointer.provenance
        (UInt64.ofNat offset) len).child with
    | mk final outcome =>
      rw [found] at childDone
      cases childDone
      rfl
  have reborrow := protected_reborrow_of_steps h options.limits.retag sourcePlace frames frame borrowFrame allocated allocatedBorrow
    rfl frameBorrow id entry (UInt64.ofNat offset) len (parent pointer.provenance)
    tracker.global.nextPointerTag ChildBorrow.fnEntryLocation ChildBorrow.fnEntryPolicy rfl rfl
    (by exact UInt64.lt_iff_toNat_lt.mpr positive)
    (by rw [ctx.source.check];exact check) (by rw [ctx.source.resolve];exact resolve)
    (by rw [ctx.source.log]) inside ctx.globalKind ctx.globals (ctx.source.ensure.trans ctx.ensure) ctx.synchronize
    sourceLive race accessed.tree output.child.tree rfl
    (by simpa only [literal,accessed,registered,GeneralBorrowFnEntryRegistration.advanced,allocatedBorrow,allocatedTracker,
      registeredGlobal,GlobalState.addProtector,ite_true] using readDone) childEq
  have retag := retag_place_at_of_reborrow h options.limits.retag sourcePlace ChildBorrow.fnEntryPolicy (Size.ofBytes len) Align.ONE
    start (Storage.withCurrent frames (registeredFrame frame borrowFrame id tracker.global.nextPointerTag)
      (installed before tracker room id entry output.child.tree)) tracker enabled room
    id pointer.provenance rfl sizing reborrow
  let changed := changedPointer pointer id tracker.global.nextPointerTag
  let value := RetagReferencePlace.sliceValue cfg.access.runtime.base pointer len ActualReferenceMetadata.reference
  let typedOutput := RetagReferencePlace.sliceValue cfg.access.runtime.base changed len ActualReferenceMetadata.reference
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
    exact RetagReferencePlace.canonical_from_immediate cfg.access ReferenceMetadataFacts.prepared () pointer len
      ActualReferenceMetadata.reference ProjectionMetadataFacts.sliceLayout dereference ActualReferenceMetadata.pointee_layout
      ProjectionMetadataFacts.slice_layout_shape.2.2
  have changedEq : TypedRetagGeneric.retaggedPlace sourcePlace id tracker.global.nextPointerTag =
      RetagReferencePlace.slicePlace changed len ProjectionMetadataFacts.sliceLayout := rfl
  have reconstruct : h.reconstruct value (TypedRetagGeneric.retaggedPlace sourcePlace id tracker.global.nextPointerTag) =
      pure typedOutput := by
    rw [ctx.source.reconstruct,changedEq]
    exact RetagReferencePlace.bound_reconstruct cfg.access h value changed len ProjectionMetadataFacts.sliceLayout
  have typed := reference_pointer_of_steps h options.limits.retag value typedOutput sourcePlace
    (TypedRetagGeneric.retaggedPlace sourcePlace id tracker.global.nextPointerTag) ProjectionMetadataFacts.sliceLayout.ty
    .Mut .FnEntry ChildBorrow.fnEntryPolicy start
    (Storage.withCurrent frames (registeredFrame frame borrowFrame id tracker.global.nextPointerTag)
      (installed before tracker room id entry output.child.tree))
    queries.shape queries.pointee_eq permission construct retag reconstruct
  refine ⟨typed,?_,?_,?_,?_,origins,?_,rfl,rfl,rfl⟩
  · rw [literalEq];rfl
  · rw [literalEq];rfl
  · rw [literalEq];rfl
  · rw [literalEq];rfl
  · exact MemoryCopyBridge.live_lookup_replaced before.memory id _

end
end DuplicatePrefix.CurrentCallTypedSourceOperation
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallTypedSourceOperation" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual typed source operation dependency {dependency}"
