import duplicate_prefix.GeneralBorrowWildcardWindowPointerChecks
import duplicate_prefix.GeneralBorrowPositiveWildcardFnEntry
import duplicate_prefix.GeneralBorrowRawWildcardFnEntryPositive
namespace DuplicatePrefix.GeneralBorrowRawWildcardWindowTypedFnEntry
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Input Miri.Interpreter
open TypedBorrowSteps ReferenceBorrowDriver
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
/-- Typed positive wildcard FnEntry retagging derives pointer checks and real
address resolution, then the raw allocation/read/root-constructor pipeline.
Full child Both Positive is retained on the exact typed installed tree. -/
theorem retag_place {K U C F A : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (sources : TypedRetagFields.SourceFields h prepared access projection vtable pointers choice)
    (budget : Nat) (place : MPlaceTy Provenance)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U)) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (tagRoom : tracker.global.nextPointerTag.value < 18446744073709551615)
    (address base len : UInt64) (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (byteBounds : (address-base).toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (pointer : place.mplace.ptr = Pointer.new (some .wildcard) (Size.ofBytes address))
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (position : Nat)
    (addressGeometry : WildcardInteriorHitAddress.Cut machine.user.addresses.intToPtrMap address (position+1))
    (insideAddress : address-base < entry.allocation.byteSize.bytes)
    (addressRow : machine.user.addresses.intToPtrMap[position]? = some ⟨base,id⟩)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (exposedAlloc : machine.user.addresses.exposed.contains id = true)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (frozen : h.typeIsFreeze place.layout.ty = pure true)
    (sizing : h.sizeAndAlign place (Storage.withCurrent frames frame machine) =
      .ok (some (Size.ofBytes len,Align.ONE)) (Storage.withCurrent frames frame machine))
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (capability : DuplicatePrefixBorrowAuthorization.Positive entry.allocation.extra tracker.global.protectedTags
      none none none (address-base) len)
    (distinct : entry.allocation.extra.roots.toList.Nodup)
    (short : entry.allocation.extra.nodes.size < 65536)
    (nodeRoom : entry.allocation.extra.nodes.size+1 ≤ 4294967295) :
    ∃ output : GeneralBorrowForestFnEntry.Output,
      GeneralBorrowRawWildcardFnEntryRuntime.operation entry.allocation.extra tracker.global borrowFrame id (address-base) len = .ok output ∧
      TypedRetag.retagPlace h budget place ChildBorrow.fnEntryPolicy (Storage.withCurrent frames frame machine) =
        .ok (TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag)
          (Storage.withCurrent frames (registeredFrame frame borrowFrame id tracker.global.nextPointerTag)
            {registeredMachine (allocatedMachine machine tracker tagRoom) (allocatedTracker tracker tagRoom) tracker.global.nextPointerTag with
              memory := RetagEntry.updatedMemory machine.memory id entry output.child.tree}) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      ∃ child,output.child.tree.indexOfTag tracker.global.nextPointerTag = some child ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive output.child.tree output.global.protectedTags
          (some child) (some child) (some tracker.global.nextPointerTag) (address-base) len) := by
  let tag := tracker.global.nextPointerTag
  let allocated := allocatedMachine machine tracker tagRoom
  let allocatedBorrow := allocatedTracker tracker tagRoom
  let tree := entry.allocation.extra
  let registration := GeneralBorrowFnEntryRegistration.registered tracker.global borrowFrame id tagRoom
  let accessed := tree.performBorrowAccessRange .wildcard (Size.ofBytes (address-base)) (Size.ofBytes len)
    .Read registration.1.protectedTags .VisitChildrenOfAccessed
  let childResult := accessed.tree.newChild (Size.ofBytes (address-base)) .wildcard tag
    (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
  let literal : GeneralBorrowForestFnEntry.Output := ⟨registration.1,registration.2,tag,accessed,childResult⟩
  obtain ⟨output,run,tagEq,globalEq,frameEq,accessDone,childDone,afterRuntime,capacity,growth,child,lookup,roots,both,geometry⟩ :=
    GeneralBorrowRawWildcardFnEntryPositive.invoke tree tracker.global borrowFrame id runtime (address-base) len capability distinct short nodeRoom tagRoom
  have operationEq : GeneralBorrowRawWildcardFnEntryRuntime.operation tree tracker.global borrowFrame id (address-base) len = .ok literal := by
    simp only [GeneralBorrowRawWildcardFnEntryRuntime.operation,TypedRetagEmpty.allocate_tag tracker.global tagRoom,
      Except.bind,Except.pure,bind,pure]
    rfl
  have normalized : output = literal := Except.ok.inj (run.symm.trans operationEq)
  subst output
  have check : h.checkPtrAccess place.mplace.ptr (Size.ofBytes len) (Storage.withCurrent frames frame allocated) =
      .ok () (Storage.withCurrent frames frame allocated) := by
    rw [sources.check,pointer]
    exact GeneralBorrowWildcardWindowPointerChecks.check pointers access _ address base len id entry position addressGeometry insideAddress addressRow
      pointerWiring width addressMode exposedAlloc cached present positive signedFits byteBounds
  have resolve : h.resolveAllocation place.mplace.ptr (Storage.withCurrent frames frame allocated) =
      .ok (some ⟨id,Size.ofBytes (address-base),.wildcard⟩) (Storage.withCurrent frames frame allocated) := by
    rw [sources.resolve,pointer]
    exact WildcardInteriorHitAddress.resolve pointers _ address base id entry position width addressMode addressGeometry addressRow insideAddress exposedAlloc cached present
  have inside := TypedRetagPolicyFields.inside_for_policy h budget place (Size.ofBytes len) ChildBorrow.fnEntryPolicy ChildBorrow.fnEntryLocation
    (ChildBorrow.mutable_fn_entry_initial_location true) sources.precise frozen
  have childEq : accessed.tree.newChild (Size.ofBytes (address-base)) .wildcard tag
      (DedupRangeMap.new (Size.ofBytes len) ChildBorrow.fnEntryLocation) (.ReservedFrz false) true =
      ⟨literal.child.tree,.ok ()⟩ := by
    change childResult = ⟨childResult.tree,.ok ()⟩
    cases found : childResult with
    | mk final outcome =>
      change childResult.outcome = .ok () at childDone
      rw [found] at childDone
      cases childDone
      rfl
  have reborrow := protected_reborrow_of_steps h budget place frames frame borrowFrame allocated allocatedBorrow rfl frameBorrow
    id entry (address-base) len .wildcard tag ChildBorrow.fnEntryLocation ChildBorrow.fnEntryPolicy rfl rfl positive check resolve
    (by rw [sources.log]) inside globalKind globals (sources.ensure.trans extraWiring) synchronize present race accessed.tree literal.child.tree
    (by rfl)
    (by simpa only [literal,accessed,registration,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,
      allocatedBorrow,allocatedTracker,registeredGlobal,GlobalState.addProtector,ite_true,tree,tag] using accessDone)
    childEq
  have typed := retag_place_at_of_reborrow h budget place ChildBorrow.fnEntryPolicy (Size.ofBytes len) Align.ONE
    (Storage.withCurrent frames frame machine)
    (Storage.withCurrent frames (registeredFrame frame borrowFrame id tag)
      {registeredMachine allocated allocatedBorrow tag with memory := RetagEntry.updatedMemory machine.memory id entry literal.child.tree})
    tracker enabled tagRoom id .wildcard (by rw [pointer];rfl) sizing reborrow
  exact ⟨literal,run,typed,afterRuntime,child,lookup,both⟩
end DuplicatePrefix.GeneralBorrowRawWildcardWindowTypedFnEntry
