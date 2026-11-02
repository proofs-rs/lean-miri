import duplicate_prefix.GeneralBorrowPositiveWildcardWindowPointerChecks
import duplicate_prefix.GeneralBorrowSparseExposedLeafRange
import duplicate_prefix.GeneralBorrowFreshReadFrame
import duplicate_prefix.GeneralBorrowPositiveWildcardConstructor
import duplicate_prefix.ReferenceBorrowDriver
import duplicate_prefix.ChildBorrow
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardWindowFnEntry
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
    (base offset len : UInt64) (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (byteBounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (pointerFits : base.toNat+offset.toNat+len.toNat<2^64)
    (pointer : place.mplace.ptr = Pointer.new (some .wildcard) (Size.ofBytes (base+offset)))
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (position : Nat) (positionValid : position < machine.user.addresses.intToPtrMap.size)
    (ordered : WildcardInteriorHitAddress.Ordered machine.user.addresses.intToPtrMap)
    (addressRow : machine.user.addresses.intToPtrMap[position]? = some ⟨base,id⟩)
    (beforeNext : ∀nextValid:position+1<machine.user.addresses.intToPtrMap.size,base+offset<machine.user.addresses.intToPtrMap[position+1].address)
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
    (treeBounds : offset.toNat+len.toNat≤entry.allocation.extra.locations.size.bytes.toNat)
    (sourceRaw : GeneralRangeMapState.Every (fun location=>GeneralBorrowSparseExposedLeafState.Raw entry.allocation.extra location
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags) entry.allocation.extra.locations)
    (tagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping tracker.global.nextPointerTag)
    (noFree : entry.allocation.extra.tagMapping.deassigned.back? = none)
    (fits : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295) :
    let tag := tracker.global.nextPointerTag
    let tree := entry.allocation.extra
    let preparedTree : BorrowTree := (tree.performBorrowAccessRange .wildcard (Size.ofBytes offset) (Size.ofBytes len) .Read (registeredGlobal tracker tag).protectedTags .VisitChildrenOfAccessed).tree
    let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    let finalTree := GeneralBorrowPositiveWildcardConstructor.result preparedTree
      ⟨tree.tagMapping.mapping.push (tag,index),tree.tagMapping.deassigned⟩ index tag
      (.ReservedFrz false) .None ChildBorrow.fnEntryLocation offset len
    TypedRetag.retagPlace h budget place ChildBorrow.fnEntryPolicy (Storage.withCurrent frames frame machine) =
      .ok (TypedRetagGeneric.retaggedPlace place id tag)
        (Storage.withCurrent frames (registeredFrame frame borrowFrame id tag)
          {registeredMachine (allocatedMachine machine tracker tagRoom) (allocatedTracker tracker tagRoom) tag with
            memory := RetagEntry.updatedMemory machine.memory id entry finalTree}) := by
  let tag := tracker.global.nextPointerTag
  let allocated := allocatedMachine machine tracker tagRoom
  let allocatedBorrow := allocatedTracker tracker tagRoom
  let tree := entry.allocation.extra
  let preparedTree : BorrowTree := (tree.performBorrowAccessRange .wildcard (Size.ofBytes offset) (Size.ofBytes len) .Read (registeredGlobal tracker tag).protectedTags .VisitChildrenOfAccessed).tree
  let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  let finalTree := GeneralBorrowPositiveWildcardConstructor.result preparedTree
    ⟨tree.tagMapping.mapping.push (tag,index),tree.tagMapping.deassigned⟩ index tag
    (.ReservedFrz false) .None ChildBorrow.fnEntryLocation offset len
  have nonzero : len ≠ 0 := by intro zero;subst len;exact UInt64.lt_irrefl 0 positive
  have bounds : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat := by simpa using treeBounds
  have owned : GeneralRangeMapOrigins.OwnedOn (fun location=>GeneralBorrowSparseExposedLeafState.Raw tree location
      (registeredGlobal tracker tag).protectedTags) offset (offset+len) tree.locations := by
    intro position valid _ _ _
    exact sourceRaw position valid
  have read := GeneralBorrowSparseExposedLeafRange.access tree (registeredGlobal tracker tag).protectedTags head extras leafGeometry
    (Size.ofBytes offset) (Size.ofBytes len) .Read .VisitChildrenOfAccessed well offset (offset+len) owned bounds (Nat.le_refl _) (Nat.le_refl _)
  have readFrame : preparedTree={tree with locations:=preparedTree.locations} := GeneralBorrowFreshReadFrame.frame tree .wildcard (Size.ofBytes offset)
    (Size.ofBytes len) .Read (registeredGlobal tracker tag).protectedTags .VisitChildrenOfAccessed
  have nextFresh : GeneralBorrowTagMap.Fresh preparedTree.tagMapping tag := by rw [readFrame];exact tagFresh
  have nextFree : preparedTree.tagMapping.deassigned.back?=none := by rw [readFrame];exact noFree
  have nextFits : preparedTree.tagMapping.mapping.size≤4294967295 := by rw [readFrame];exact fits
  have nextBounds : offset.toNat+len.toNat≤preparedTree.locations.size.bytes.toNat := by rw [read.2.2.2];exact bounds
  have child := GeneralBorrowPositiveWildcardConstructor.append preparedTree tag nextFresh nextFree nextFits
    (.ReservedFrz false) .None ChildBorrow.fnEntryLocation true rfl rfl rfl rfl rfl offset len nonzero read.2.2.1 nextBounds
  have sameMapping : preparedTree.tagMapping=tree.tagMapping := by simpa only using congrArg BorrowTree.tagMapping readFrame
  rw [sameMapping] at child
  have geometry := GeneralBorrowPositiveWildcardWindowPointerChecks.geometry machine.user.addresses.intToPtrMap base offset len id entry.allocation.byteSize
    position positionValid ordered addressRow beforeNext positive byteBounds pointerFits
  have check : h.checkPtrAccess place.mplace.ptr (Size.ofBytes len) (Storage.withCurrent frames frame allocated) =
      .ok () (Storage.withCurrent frames frame allocated) := by
    rw [sources.check,pointer]
    exact GeneralBorrowPositiveWildcardWindowPointerChecks.check pointers access _ base offset len id entry geometry
      pointerWiring width addressMode exposedAlloc cached present positive signedFits byteBounds
  have resolve : h.resolveAllocation place.mplace.ptr (Storage.withCurrent frames frame allocated) =
      .ok (some ⟨id,Size.ofBytes offset,.wildcard⟩) (Storage.withCurrent frames frame allocated) := by
    rw [sources.resolve,pointer]
    have resolved := WildcardGeneralHitReborrow.resolve pointers (Storage.withCurrent frames frame allocated) (base+offset) base id entry
      geometry width addressMode exposedAlloc cached present
    simpa only [UInt64.add_comm base offset,UInt64.add_sub_cancel] using resolved
  have inside := TypedRetagPolicyFields.inside_for_policy h budget place (Size.ofBytes len) ChildBorrow.fnEntryPolicy ChildBorrow.fnEntryLocation
    (ChildBorrow.mutable_fn_entry_initial_location true) sources.precise frozen
  have reborrow := protected_reborrow_of_steps h budget place frames frame borrowFrame allocated allocatedBorrow rfl frameBorrow
    id entry offset len .wildcard tag ChildBorrow.fnEntryLocation ChildBorrow.fnEntryPolicy rfl rfl positive check resolve
    (by rw [sources.log]) inside globalKind globals (sources.ensure.trans extraWiring) synchronize present race preparedTree finalTree
    (by rfl)
    (by simpa only [preparedTree,tree,allocatedBorrow,allocatedTracker,registeredGlobal,Size.ofBytes] using read.1)
    child
  exact retag_place_at_of_reborrow h budget place ChildBorrow.fnEntryPolicy (Size.ofBytes len) Align.ONE
    (Storage.withCurrent frames frame machine)
    (Storage.withCurrent frames (registeredFrame frame borrowFrame id tag)
      {registeredMachine allocated allocatedBorrow tag with memory := RetagEntry.updatedMemory machine.memory id entry finalTree})
    tracker enabled tagRoom id .wildcard (by rw [pointer];rfl) sizing reborrow
end DuplicatePrefix.GeneralBorrowPositiveWildcardWindowFnEntry
