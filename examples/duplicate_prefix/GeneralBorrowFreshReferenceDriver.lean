import duplicate_prefix.ReferenceBorrowDriver
import duplicate_prefix.GeneralBorrowFreshReborrowStages
namespace DuplicatePrefix.GeneralBorrowFreshReferenceDriver
open Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures
open Miri.TreeBorrows Miri.Input Miri.Interpreter
open DuplicatePrefix.GeneralBorrowFreshReborrowStages
open DuplicatePrefix.ReferenceBorrowDriver (allocatedMachine allocatedTracker)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def policy : Kind → RetagPolicy.NewPermission
  | .mutable => ⟨.ReservedFrz false,.ReservedFrz false,.ReservedFrz false,some .StrongProtector⟩
  | .shared => ⟨.Frozen,.Cell,.Frozen,some .StrongProtector⟩
def mutability : Kind → Miri.MIR.Mutability
  | .mutable => .Mut
  | .shared => .Not
private theorem protected_policy (kind : Kind) : (policy kind).protector = some .StrongProtector := by cases kind <;> rfl
private theorem associated (kind : Kind) : (initial kind).permission.associatedAccess = some .Read := by cases kind <;> rfl
private theorem initial_state (kind : Kind) : RetagPolicy.initialLocationState (policy kind) true = .ok (initial kind) := by cases kind <;> rfl
private theorem outside_policy (kind : Kind) : (policy kind).outsidePermission = outside kind := by cases kind <;> rfl
private theorem created_policy (kind : Kind) :
    RetagPolicy.create ⟨true,true,true⟩ (if mutability kind == .Mut then .Mutable else .Shared) .FnEntry ⟨false,false⟩ = some (policy kind) := by
  cases kind <;> rfl

/-- The real FnEntry reference driver derives protector registration, parent
read and child completion from explicit tree/allocator data. Runtime/compiler
hook wiring, pointer metadata, race configuration and positive slice bounds
remain explicit. No successful read or successful child operation is assumed. -/
theorem protected_reference_pointer {K U C F A : Type} [DecidableEq K]
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
    (enabled : machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (base offset len : UInt64) (parentTag : BorTag) (tag : BorTag)
    (tagEq : tag = tracker.global.nextPointerTag)
    (kind : GeneralBorrowFreshReborrowStages.Kind)
    (positive : (0 : UInt64) < len)
    (frozen : h.typeIsFreeze place.layout.ty = pure true)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id parentTag)) (Size.ofBytes (base + offset)))
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (race : machine.dataRace = none)
    (parent root : UniIndex) (parentNode : TreeNode)
    (depth : GeneralBorrowExposure.ParentDepth entry.allocation.extra.nodes)
    (children : GeneralBorrowGraph.ChildNodes entry.allocation.extra)
    (parentPresent : entry.allocation.extra.nodeAt parent = some parentNode)
    (roots : entry.allocation.extra.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover entry.allocation.extra)
    (parentTagPresent : entry.allocation.extra.indexOfTag parentTag = some parent)
    (tagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping tag)
    (protectorFresh : GeneralBorrowProtector.Fresh entry.allocation.extra tag)
    (nodeFits : entry.allocation.extra.nodes.data.size ≤ 4294967296)
    (slot : GeneralBorrowFreshReborrowStages.Slot entry.allocation.extra depth parent)
    (well : entry.allocation.extra.locations.WellFormed)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (GeneralBorrowRange.LocationOwned entry.allocation.extra tracker.global.protectedTags parent
        (GeneralBorrowFreshReborrowStages.ownerKind kind)) offset (offset+len) entry.allocation.extra.locations)
    (reference : LocalLayout)
    (shape : h.typeShape reference.ty = pure .reference)
    (pointeeQuery : h.referencePointee reference.ty = pure (place.layout.ty,mutability kind))
    (unpin : h.isUnpin place.layout.ty = pure true)
    (unsafeUnpin : h.isUnsafeUnpin place.layout.ty = pure true)
    (dereference : CompilerFacts.builtinDeref prepared.context reference.ty true = .ok (some place.layout.ty))
    (pointeeLayout : CompilerFacts.layoutOf prepared.context place.layout.ty = .ok place.layout)
    (pointeeAlign : place.layout.layout.align.abi = Align.ONE)
    (placeShape : place = RetagReferencePlace.slicePlace
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len place.layout)
    (sliceFacts : TypedRetagEntry.SliceFacts projection choice place len) :
    ∃ (finalTree : BorrowTree) (index : UniIndex),
    TypedRetag.retagPtrValue h budget
      (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len reference)
      reference.ty .FnEntry (Storage.withCurrent frames frame machine) =
      .ok (some (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))) len reference))
      (Storage.withCurrent frames (TypedBorrowSteps.registeredFrame frame borrowFrame id tag)
        {TypedBorrowSteps.registeredMachine (allocatedMachine machine tracker fresh) (allocatedTracker tracker fresh) tag
          with memory := RetagEntry.updatedMemory machine.memory id entry finalTree}) ∧
      GeneralRangeMapOrigins.OwnedOn
        (GeneralBorrowRange.LocationOwned finalTree (TypedBorrowSteps.registeredGlobal tracker tag).protectedTags
          index (GeneralBorrowFreshReborrowStages.ownerKind kind)) offset (offset+len) finalTree.locations := by
  let read := entry.allocation.extra.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset)
    (Size.ofBytes len) .Read (TypedBorrowSteps.registeredGlobal tracker tag).protectedTags .VisitChildrenOfAccessed
  let child := read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) tag
    (DedupRangeMap.new (Size.ofBytes len) (initial kind)) (outside kind) true
  have treeBounds : offset.toNat+len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat := by
    rw [capacity]
    exact bounds
  have nonzero : len ≠ 0 := by intro equal;rw [equal] at positive;simp at positive
  have stages := GeneralBorrowFreshReborrowStages.protected_construct entry.allocation.extra tracker.global.protectedTags kind
    parentTag tag parent root parentNode depth children parentPresent roots covered parentTagPresent tagFresh protectorFresh
    nodeFits slot offset len nonzero well treeBounds owned
  change ∃ index, read.status = .Completed ∧ child.outcome = .ok () ∧
    GeneralRangeMapOrigins.OwnedOn
      (GeneralBorrowRange.LocationOwned child.tree (TypedBorrowSteps.registeredGlobal tracker tag).protectedTags
        index (ownerKind kind)) offset (offset+len) child.tree.locations at stages
  obtain ⟨index,readDone,childDone,childOwned⟩ := stages
  have childEq : read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) tag
      (DedupRangeMap.new (Size.ofBytes len) (initial kind)) (policy kind).outsidePermission (policy kind).protector.isSome =
      ⟨child.tree,.ok ()⟩ := by
    rw [outside_policy,protected_policy]
    exact GeneralBorrowFreshReborrowStages.child_complete child childDone
  have sizingFunction := TypedRetagFields.size_from_fields h prepared access projection vtable pointers choice sources place len sliceFacts
  have sizing : h.sizeAndAlign place (Storage.withCurrent frames frame machine) =
      .ok (some (Size.ofBytes len,Align.ONE)) (Storage.withCurrent frames frame machine) := by
    rw [sizingFunction]
    rfl
  refine ⟨child.tree,index,?_,childOwned⟩
  exact ReferenceBorrowDriver.protected_reference_pointer
    (h := h)
    (prepared := prepared)
    (access := access)
    (projection := projection)
    (vtable := vtable)
    (pointers := pointers)
    (choice := choice)
    (sources := sources)
    (budget := budget)
    (place := place)
    (frames := frames)
    (frame := frame)
    (borrowFrame := borrowFrame)
    (machine := machine)
    (tracker := tracker)
    (enabled := enabled)
    (fresh := fresh)
    (frameBorrow := frameBorrow)
    (id := id)
    (entry := entry)
    (base := base)
    (offset := offset)
    (len := len)
    (parentTag := parentTag)
    (tag := tag)
    (tagEq := tagEq)
    (initial := initial kind)
    (policy := policy kind)
    (protection := protected_policy kind)
    (associated := associated kind)
    (positive := positive)
    (frozen := frozen)
    (initialState := initial_state kind)
    (pointer := pointer)
    (pointerWiring := pointerWiring)
    (width := width)
    (cached := cached)
    (signedFits := signedFits)
    (bounds := bounds)
    (globalKind := globalKind)
    (globals := globals)
    (extraWiring := extraWiring)
    (synchronize := synchronize)
    (present := present)
    (race := race)
    (parentTree := read.tree)
    (finalTree := child.tree)
    (readTree := rfl)
    (readDone := readDone)
    (child := childEq)
    (reference := reference)
    (mutability := mutability kind)
    (mode := .FnEntry)
    (created := created_policy kind)
    (shape := shape)
    (pointeeQuery := pointeeQuery)
    (unpin := unpin)
    (unsafeUnpin := unsafeUnpin)
    (dereference := dereference)
    (pointeeLayout := pointeeLayout)
    (pointeeAlign := pointeeAlign)
    (placeShape := placeShape)
    (sizing := sizing)
end DuplicatePrefix.GeneralBorrowFreshReferenceDriver
#print axioms DuplicatePrefix.GeneralBorrowFreshReferenceDriver.protected_reference_pointer
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshReferenceDriver." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected reference driver dependency {dependency}"
