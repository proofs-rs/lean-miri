import duplicate_prefix.CurrentCallEmptyMaterializedWildcard

namespace DuplicatePrefix.CurrentCallEmptyMaterializedWildcardPointer
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter Miri.TreeBorrows Miri.DataStructures
open CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata TypedBorrowSteps ReferenceBorrowDriver
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

theorem retag_pointer (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (actualPointers : ctx.pointers = GlobalDataOnlyActualConfig.pointers PreparedReflection.actual.compiler
      PreparedReflection.actual.image (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions) ())
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (root : BorTag) (base offset : UInt64)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (distinct : root ≠ tracker.global.nextPointerTag)
    (info : AllocationInfo) (infoEq : machine.memory.getAllocInfo id=.ok info) (dataKind : info.kind=.liveData)
    (after : RootState) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (capacity : Size)
    (ensure : (config options remaining span).retag.ensureTreeExtra id
      (registeredState frames frame borrowFrame (allocatedMachine machine tracker fresh) (allocatedTracker tracker fresh)
        id tracker.global.nextPointerTag)=.ok () after)
    (present : after.machine.memory.live.find? (fun row=>row.1==id)=some (id,entry))
    (rootShape : entry.allocation.extra=BorrowTree.new root capacity)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (geometry : WildcardGeneralHitReborrow.Geometry machine.user.addresses.intToPtrMap (base+offset) base id info.size)
    (exposed : machine.user.addresses.exposed.contains id = true)
    (allocLive : machine.memory.isAllocLive id = true)
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false) :
    TypedRetag.retagPtrValue (adapted options remaining span ctx.pointers) options.limits.retag
        (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new .wildcard (Size.ofBytes (base+offset))) 0 reference)
        reference.ty .FnEntry (Storage.withCurrent frames frame machine) =
        .ok (some (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 reference))
          (CurrentCallEmptyMaterializedBorrow.completed after id entry
            (CurrentCallEmptyMaterializedWildcard.finalTree root tracker.global.nextPointerTag capacity)) := by
  let h := adapted options remaining span ctx.pointers
  let before := Storage.withCurrent frames frame machine
  let place := RetagReferencePlace.slicePlace
    (Pointer.new .wildcard (Size.ofBytes (base+offset))) 0 pointee
  let oldPointer := Pointer.new Provenance.wildcard (Size.ofBytes (base+offset))
  let newPointer := Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))
  let value := RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base oldPointer 0 reference
  let output := RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base newPointer 0 reference
  have queries := reference_queries options remaining span ctx.pointers
  have sizing : h.sizeAndAlign place before = .ok (some (Size.ZERO,Align.ONE)) before := by
    rw [←ctx.visitor.sizing]
    exact ProjectionMetadataFacts.actual_validity_size_at options remaining span cmp before dynamicFuel fuelEq 0
      metadata notConstructed (by decide) place rfl rfl
  have reborrow:=CurrentCallEmptyMaterializedWildcard.reborrow options remaining span ctx actualPointers
    frames frame borrowFrame frameBorrow (allocatedMachine machine tracker fresh) (allocatedTracker tracker fresh) rfl
    id root tracker.global.nextPointerTag base offset info infoEq dataKind cachedAddress addressMode geometry exposed allocLive distinct
    after entry capacity ensure present rootShape
  let final:=CurrentCallEmptyMaterializedBorrow.completed after id entry
    (CurrentCallEmptyMaterializedWildcard.finalTree root tracker.global.nextPointerTag capacity)
  have retag := TypedBorrowSteps.retag_place_at_of_reborrow h options.limits.retag place ChildBorrow.fnEntryPolicy
    Size.ZERO Align.ONE before final tracker enabled fresh id .wildcard rfl sizing reborrow
  have permission := TypedRetagPolicyFields.new_permission_general h pointee.ty .Mutable .FnEntry before frames frame rfl
    queries.unpin queries.unsafeUnpin queries.freeze ctx.source.implicitWrites
  have created : RetagPolicy.create ⟨true,true,true⟩ .Mutable .FnEntry ⟨false,false⟩ =
      some ChildBorrow.fnEntryPolicy := by decide
  rw [created] at permission
  have construct : h.immPtrToMPlace value = pure place := by
    rw [ctx.source.construct]
    exact RetagReferencePlace.canonical_from_immediate (config options remaining span).access
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts () oldPointer 0 reference pointee
      (by rw [reference_ty,pointee_ty]; exact RootMetadataQueries.mutable_slice_dereference)
      (by rw [pointee_ty]; exact pointee_layout) ProjectionMetadataFacts.slice_layout_shape.2.2
  have changed : TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag =
      RetagReferencePlace.slicePlace newPointer 0 pointee := rfl
  have reconstruct : h.reconstruct value (TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag) =
      pure output := by
    rw [ctx.source.reconstruct,changed]
    exact RetagReferencePlace.bound_reconstruct (config options remaining span).access h value newPointer 0 pointee
  exact TypedBorrowSteps.reference_pointer_of_steps h options.limits.retag value output place
    (TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag) pointee.ty .Mut .FnEntry ChildBorrow.fnEntryPolicy
    before final queries.shape queries.pointee_eq permission construct retag reconstruct
end
end DuplicatePrefix.CurrentCallEmptyMaterializedWildcardPointer
