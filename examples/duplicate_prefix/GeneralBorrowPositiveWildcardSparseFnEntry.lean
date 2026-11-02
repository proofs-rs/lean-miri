import duplicate_prefix.GeneralBorrowPositiveWildcardPointerChecks
import duplicate_prefix.GeneralBorrowSparseExposedLeafRange
import duplicate_prefix.GeneralBorrowFreshReadFrame
import duplicate_prefix.GeneralBorrowPositiveWildcardConstructor
import duplicate_prefix.ReferenceBorrowDriver
import duplicate_prefix.ChildBorrow
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardSparseFnEntry
open Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Input Miri.Interpreter
open DuplicatePrefix.TypedBorrowSteps DuplicatePrefix.ReferenceBorrowDriver
open DuplicatePrefix.GeneralBorrowWildcardLeaf DuplicatePrefix.GeneralBorrowExposureCardinality
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Physical positive-length wildcard FnEntry borrowing hook for arbitrary well-formed allocation partitions. Actual global
tag allocation, Strong frame/global registration, pointer validation and live
allocation resolution precede the actual wildcard Read and root constructor.
Every operation result is derived from initial source wiring, raw ordered
address rows, allocation metadata and exposed-leaf permission/cache resources.
This is the typed retagPlace driver, not the full recursive reference validator. -/
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
    (base len : UInt64) (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (byteBounds : len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (pointer : place.mplace.ptr = Pointer.new (some .wildcard) (Size.ofBytes base))
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (position : Nat) (positionValid : position < machine.user.addresses.intToPtrMap.size)
    (ordered : WildcardInteriorHitAddress.Ordered machine.user.addresses.intToPtrMap)
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
    (head : UniIndex) (extras : List UniIndex)
    (leafGeometry : GeneralBorrowSparseExposedLeafState.Geometry entry.allocation.extra head extras)
    (well : entry.allocation.extra.locations.WellFormed)
    (treeBounds : len.toNat≤entry.allocation.extra.locations.size.bytes.toNat)
    (sourceRaw : GeneralRangeMapState.Every (fun location=>GeneralBorrowSparseExposedLeafState.Raw entry.allocation.extra location
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags) entry.allocation.extra.locations)
    (tagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping tracker.global.nextPointerTag)
    (noFree : entry.allocation.extra.tagMapping.deassigned.back? = none)
    (fits : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295) :
    let tag := tracker.global.nextPointerTag
    let tree := entry.allocation.extra
    let preparedTree : BorrowTree := (tree.performBorrowAccessRange .wildcard Size.ZERO (Size.ofBytes len) .Read (registeredGlobal tracker tag).protectedTags .VisitChildrenOfAccessed).tree
    let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    let finalTree := GeneralBorrowPositiveWildcardConstructor.result preparedTree
      ⟨tree.tagMapping.mapping.push (tag,index),tree.tagMapping.deassigned⟩ index tag
      (.ReservedFrz false) .None ChildBorrow.fnEntryLocation 0 len
    TypedRetag.retagPlace h budget place ChildBorrow.fnEntryPolicy (Storage.withCurrent frames frame machine) =
      .ok (TypedRetagGeneric.retaggedPlace place id tag)
        (Storage.withCurrent frames (registeredFrame frame borrowFrame id tag)
          {registeredMachine (allocatedMachine machine tracker tagRoom) (allocatedTracker tracker tagRoom) tag with
            memory := RetagEntry.updatedMemory machine.memory id entry finalTree}) := by
  let tag := tracker.global.nextPointerTag
  let allocated := allocatedMachine machine tracker tagRoom
  let allocatedBorrow := allocatedTracker tracker tagRoom
  let tree := entry.allocation.extra
  let preparedTree : BorrowTree := (tree.performBorrowAccessRange .wildcard Size.ZERO (Size.ofBytes len) .Read (registeredGlobal tracker tag).protectedTags .VisitChildrenOfAccessed).tree
  let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  let finalTree := GeneralBorrowPositiveWildcardConstructor.result preparedTree
    ⟨tree.tagMapping.mapping.push (tag,index),tree.tagMapping.deassigned⟩ index tag
    (.ReservedFrz false) .None ChildBorrow.fnEntryLocation 0 len
  have nonzero : len ≠ 0 := by intro zero;subst len;exact UInt64.lt_irrefl 0 positive
  have bounds : (0 : UInt64).toNat+len.toNat≤tree.locations.size.bytes.toNat := by simpa using treeBounds
  have owned : GeneralRangeMapOrigins.OwnedOn (fun location=>GeneralBorrowSparseExposedLeafState.Raw tree location
      (registeredGlobal tracker tag).protectedTags) 0 len tree.locations := by
    intro position valid _ _ _
    exact sourceRaw position valid
  have read := GeneralBorrowSparseExposedLeafRange.access tree (registeredGlobal tracker tag).protectedTags head extras leafGeometry
    Size.ZERO (Size.ofBytes len) .Read .VisitChildrenOfAccessed well 0 len owned bounds (by simp [Size.ZERO]) (by simpa only [Size.ZERO,Size.ofBytes,UInt64.zero_add] using (Nat.le_refl len.toNat))
  have readFrame : preparedTree={tree with locations:=preparedTree.locations} := GeneralBorrowFreshReadFrame.frame tree .wildcard Size.ZERO
    (Size.ofBytes len) .Read (registeredGlobal tracker tag).protectedTags .VisitChildrenOfAccessed
  have nextFresh : GeneralBorrowTagMap.Fresh preparedTree.tagMapping tag := by rw [readFrame];exact tagFresh
  have nextFree : preparedTree.tagMapping.deassigned.back?=none := by rw [readFrame];exact noFree
  have nextFits : preparedTree.tagMapping.mapping.size≤4294967295 := by rw [readFrame];exact fits
  have nextBounds : (0 : UInt64).toNat+len.toNat≤preparedTree.locations.size.bytes.toNat := by rw [read.2.2.2];exact bounds
  have child := GeneralBorrowPositiveWildcardConstructor.append preparedTree tag nextFresh nextFree nextFits
    (.ReservedFrz false) .None ChildBorrow.fnEntryLocation true rfl rfl rfl rfl rfl 0 len nonzero read.2.2.1 nextBounds
  have sameMapping : preparedTree.tagMapping=tree.tagMapping := by simpa only using congrArg BorrowTree.tagMapping readFrame
  rw [sameMapping] at child
  have check : h.checkPtrAccess place.mplace.ptr (Size.ofBytes len) (Storage.withCurrent frames frame allocated) =
      .ok () (Storage.withCurrent frames frame allocated) := by
    rw [sources.check,pointer]
    exact GeneralBorrowPositiveWildcardPointerChecks.check pointers access _ base len id entry position positionValid ordered addressRow
      pointerWiring width addressMode exposedAlloc cached present positive signedFits byteBounds
  have resolve : h.resolveAllocation place.mplace.ptr (Storage.withCurrent frames frame allocated) =
      .ok (some ⟨id,Size.ofBytes 0,.wildcard⟩) (Storage.withCurrent frames frame allocated) := by
    rw [sources.resolve,pointer]
    exact WildcardOrderedHitAddress.resolve pointers _ base id entry position positionValid ordered addressRow width addressMode exposedAlloc cached present
  have inside := TypedRetagPolicyFields.inside_for_policy h budget place (Size.ofBytes len) ChildBorrow.fnEntryPolicy ChildBorrow.fnEntryLocation
    (ChildBorrow.mutable_fn_entry_initial_location true) sources.precise frozen
  have reborrow := protected_reborrow_of_steps h budget place frames frame borrowFrame allocated allocatedBorrow rfl frameBorrow
    id entry 0 len .wildcard tag ChildBorrow.fnEntryLocation ChildBorrow.fnEntryPolicy rfl rfl positive check resolve
    (by rw [sources.log]) inside globalKind globals (sources.ensure.trans extraWiring) synchronize present race preparedTree finalTree
    (by rfl)
    (by simpa only [preparedTree,tree,allocatedBorrow,allocatedTracker,registeredGlobal,Size.ZERO,Size.ofBytes] using read.1)
    child
  exact retag_place_at_of_reborrow h budget place ChildBorrow.fnEntryPolicy (Size.ofBytes len) Align.ONE
    (Storage.withCurrent frames frame machine)
    (Storage.withCurrent frames (registeredFrame frame borrowFrame id tag)
      {registeredMachine allocated allocatedBorrow tag with memory := RetagEntry.updatedMemory machine.memory id entry finalTree})
    tracker enabled tagRoom id .wildcard (by rw [pointer];rfl) sizing reborrow
end DuplicatePrefix.GeneralBorrowPositiveWildcardSparseFnEntry
