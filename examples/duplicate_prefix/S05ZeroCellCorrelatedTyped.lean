import duplicate_prefix.S05ZeroCellTypedGeneratedPrefix
import duplicate_prefix.TypedBorrowSteps
import duplicate_prefix.S05ZeroSizedSharedNonFreezeRetag

/-! Typed source specializations at the generated A/B/D/V/W stages. These are
local lemmas, not a composed machine-prefix theorem: a single stateful bind,
reference validation, and caller-lifetime adequacy remain separate obligations.
The auxiliary metadata is not substituted into any running state. -/
namespace DuplicatePrefix.S05ZeroCellCorrelatedTyped
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Input Miri.Interpreter
open S05ZeroCellTypedGeneratedPrefix
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

def mutablePolicy : RetagPolicy.NewPermission :=
  ⟨.ReservedFrz false,.ReservedIM,.ReservedFrz false,none⟩
def mutableInput (stage : Bool) : BorrowTree := if stage then secondWrite.tree else a.tree
def mutableRead (stage : Bool) := if stage then wRead else dRead
def mutableResult (stage : Bool) : BorrowTree := if stage then w.tree else d.tree
def mutableParent (stage : Bool) : BorTag := if stage then tag 4 else tag 2
def mutableTag (stage : Bool) : BorTag := if stage then tag 6 else tag 3

def cellInput (stage : Bool) : BorrowTree := if stage then firstWrite.tree else S05ZeroCellTypedGeneratedPrefix.exposed.tree
def cellTag (stage : Bool) : BorTag := if stage then tag 4 else tag 2

theorem cell_result_tree (stage : Bool) :
    S05ZeroSizedSharedNonFreezeRetag.resultTree (cellInput stage) (cellTag stage) =
      (if stage then b.tree else a.tree) := by cases stage <;> cbv

theorem cell_pointer_from_fields {K U C F A : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (sources : TypedRetagFields.SourceFields h prepared access projection vtable pointers choice)
    (budget : Nat) (reference pointee : LocalLayout)
    (shape : h.typeShape reference.ty = pure .reference)
    (pointeeQuery : h.referencePointee reference.ty = pure (pointee.ty,.Not))
    (unpinValue unsafeUnpinValue : Bool)
    (unpin : h.isUnpin pointee.ty = pure unpinValue)
    (unsafeUnpin : h.isUnsafeUnpin pointee.ty = pure unsafeUnpinValue)
    (nonfreeze : h.typeIsFreeze pointee.ty = pure false)
    (dereference : CompilerFacts.builtinDeref prepared.context reference.ty true = .ok (some pointee.ty))
    (pointeeLayout : CompilerFacts.layoutOf prepared.context pointee.ty = .ok pointee)
    (sized : pointee.layout.isSized = true) (zero : pointee.layout.size = Size.ZERO)
    (align : pointee.layout.align.abi = Align.ONE)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U)) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (tagRoom : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K) (address base : UInt64)
    (_nonnull : address ≠ 0)
    (geometry : WildcardGeneralHitReborrow.Geometry machine.user.addresses.intToPtrMap address base id entry.allocation.byteSize)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (mode : machine.user.addresses.provenanceMode ≠ .strict)
    (exposed : machine.user.addresses.exposed.contains id = true)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (stage : Bool)
    (tree : entry.allocation.extra = cellInput stage)
    (next : tracker.global.nextPointerTag = cellTag stage)
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}}) :
    TypedRetag.retagPtrValue h budget (S05ZeroSizedSharedNonFreezeRetag.value access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) reference)
      reference.ty .Default (Storage.withCurrent frames frame machine) =
      .ok (some (S05ZeroSizedSharedNonFreezeRetag.value access.runtime.base (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes address)) reference))
        (Storage.withCurrent frames frame
          {(ReferenceBorrowDriver.allocatedMachine machine tracker tagRoom) with
            memory := RetagEntry.updatedMemory machine.memory id entry (S05ZeroSizedSharedNonFreezeRetag.resultTree entry.allocation.extra tracker.global.nextPointerTag)}) := by
  apply S05ZeroSizedSharedNonFreezeRetag.retag_pointer h prepared access projection vtable pointers choice sources
    budget reference pointee shape pointeeQuery unpinValue unsafeUnpinValue unpin unsafeUnpin nonfreeze
    dereference pointeeLayout sized zero align frames frame machine tracker enabled tagRoom id entry address base
    _nonnull geometry width mode exposed cached present
    (globalKind := globalKind) (globals := globals)
  · rw [tree,next]
    cases stage <;> cbv <;> simp_all
  · rw [tree]
    cases stage <;> cbv
  · rw [tree]
    cases stage <;> cbv
  · exact extraWiring
  · exact synchronize

theorem mutable_from_fields {K U C F A : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (sources : TypedRetagFields.SourceFields h prepared access projection vtable pointers choice)
    (budget : Nat) (place : MPlaceTy Provenance)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U)) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (base : UInt64) (stage : Bool)
    (tree : entry.allocation.extra = mutableInput stage)
    (protections : tracker.global.protectedTags = {})
    (frozen : h.typeIsFreeze place.layout.ty = pure true)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id (mutableParent stage))) (Size.ofBytes (base + (0 : UInt64))))
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (signedFits : (2 : UInt64).toNat < 9223372036854775808)
    (bounds : (0 : UInt64).toNat + (2 : UInt64).toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (race : machine.dataRace = none) :
    TypedRetag.reborrow h budget place (Size.ofBytes (2 : UInt64)) mutablePolicy (mutableTag stage) (Storage.withCurrent frames frame machine) =
      .ok (some (.concrete id (mutableTag stage)))
        (Storage.withCurrent frames frame
          {machine with memory := RetagEntry.updatedMemory machine.memory id entry (mutableResult stage)}) := by
  apply TypedBorrowSteps.unprotected_read_from_fields h prepared access projection vtable pointers choice sources
    budget place frames frame machine tracker enabled id entry base 0 2 (mutableParent stage) (mutableTag stage)
    mutable mutablePolicy rfl rfl (by decide) frozen (by rfl) pointer pointerWiring width cached
    signedFits bounds globalKind globals extraWiring synchronize present race
    (mutableRead stage).tree (mutableResult stage)
  · rw [tree,protections]
    cases stage <;> rfl
  · rw [tree,protections]
    cases stage <;> cbv
  · cases stage <;> cbv

theorem zero_v_from_fields {K U C F A : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (sources : TypedRetagFields.SourceFields h prepared access projection vtable pointers choice)
    (budget : Nat) (place : MPlaceTy Provenance)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U)) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (base : UInt64) (tree : entry.allocation.extra = b.tree)
    (frozen : h.typeIsFreeze place.layout.ty = pure true)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id (tag 3))) (Size.ofBytes (base + 0)))
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry)) :
    TypedRetag.reborrow h budget place Size.ZERO mutablePolicy (tag 5) (Storage.withCurrent frames frame machine) =
      .ok (some (.concrete id (tag 5)))
        (Storage.withCurrent frames frame
          {machine with memory := RetagEntry.updatedMemory machine.memory id entry v.tree}) := by
  have check : h.checkPtrAccess place.mplace.ptr Size.ZERO (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames frame machine) := by
    rw [sources.check]
    exact RetagPointerChecks.check_pointer_zero access _ _
  have resolve : h.resolveAllocation place.mplace.ptr (Storage.withCurrent frames frame machine) =
      .ok (some ⟨id,Size.ZERO,.concrete (tag 3)⟩) (Storage.withCurrent frames frame machine) := by
    rw [sources.resolve,pointer]
    exact RetagPointerChecks.resolve_allocation_cached pointers _ id (tag 3) base 0 width cached
  have inside := TypedRetagPolicyFields.inside_for_policy h budget place Size.ZERO mutablePolicy mutable
    (by rfl) sources.precise frozen
  apply TypedBorrowSteps.unprotected_live_zero_of_steps h budget place frames frame machine tracker enabled
    id entry 0 (.concrete (tag 3)) (tag 5) mutable mutablePolicy rfl check resolve
    (by rw [sources.log]) inside globalKind globals (sources.ensure.trans extraWiring) synchronize present v.tree
  rw [tree]
  cbv

theorem mutable_pointer_from_fields {K U C F A : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (sources : TypedRetagFields.SourceFields h prepared access projection vtable pointers choice)
    (budget : Nat) (place : MPlaceTy Provenance)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U)) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (base : UInt64) (stage : Bool)
    (tree : entry.allocation.extra = mutableInput stage)
    (protections : tracker.global.protectedTags = {})
    (next : tracker.global.nextPointerTag = mutableTag stage)
    (frozen : h.typeIsFreeze place.layout.ty = pure true)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id (mutableParent stage))) (Size.ofBytes (base + (0 : UInt64))))
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (signedFits : (2 : UInt64).toNat < 9223372036854775808)
    (bounds : (0 : UInt64).toNat + (2 : UInt64).toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (race : machine.dataRace = none)
    (reference : LocalLayout)
    (shape : h.typeShape reference.ty = pure .reference)
    (pointeeQuery : h.referencePointee reference.ty = pure (place.layout.ty,.Mut))
    (unpin : h.isUnpin place.layout.ty = pure true)
    (unsafeUnpin : h.isUnsafeUnpin place.layout.ty = pure true)
    (dereference : CompilerFacts.builtinDeref prepared.context reference.ty true = .ok (some place.layout.ty))
    (pointeeLayout : CompilerFacts.layoutOf prepared.context place.layout.ty = .ok place.layout)
    (pointeeAlign : place.layout.layout.align.abi = Align.ONE)
    (placeShape : place = RetagReferencePlace.slicePlace
      (Pointer.new (.concrete id (mutableParent stage)) (Size.ofBytes (base+(0 : UInt64)))) (2 : UInt64) place.layout)
    (slice : TypedRetagEntry.SliceFacts projection choice place (2 : UInt64)) :
    TypedRetag.retagPtrValue h budget
      (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id (mutableParent stage)) (Size.ofBytes (base+(0 : UInt64)))) (2 : UInt64) reference)
      reference.ty .Default (Storage.withCurrent frames frame machine) =
      .ok (some (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id (mutableTag stage)) (Size.ofBytes (base+(0 : UInt64)))) (2 : UInt64) reference))
      (Storage.withCurrent frames frame
        {ReferenceBorrowDriver.allocatedMachine machine tracker fresh
          with memory := RetagEntry.updatedMemory machine.memory id entry (mutableResult stage)}) := by
  have sizing := congrFun (TypedRetagFields.size_from_fields h prepared access projection vtable pointers choice sources place _ slice)
    (Storage.withCurrent frames frame machine)
  let before := Storage.withCurrent frames frame machine
  let after := Storage.withCurrent frames frame
    {ReferenceBorrowDriver.allocatedMachine machine tracker fresh
      with memory := RetagEntry.updatedMemory machine.memory id entry (mutableResult stage)}
  let oldPointer := Pointer.new (Provenance.concrete id (mutableParent stage)) (Size.ofBytes (base+(0 : UInt64)))
  let newPointer := Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+(0 : UInt64)))
  let value := RetagReferencePlace.sliceValue access.runtime.base oldPointer (2 : UInt64) reference
  let output := RetagReferencePlace.sliceValue access.runtime.base newPointer (2 : UInt64) reference
  have reborrow := mutable_from_fields h prepared access projection vtable pointers choice sources
    budget place frames frame (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
    (ReferenceBorrowDriver.allocatedTracker tracker fresh) rfl id entry base stage tree protections frozen
    pointer pointerWiring width cached signedFits bounds globalKind globals extraWiring synchronize present race
  have allocatedNext : tracker.global.nextPointerTag = mutableTag stage := next
  rw [← allocatedNext] at reborrow
  have retag := TypedBorrowSteps.retag_place_at_of_reborrow h budget place mutablePolicy (Size.ofBytes (2 : UInt64)) Align.ONE
    before after tracker enabled fresh id (.concrete id (mutableParent stage)) (by rw [pointer]; rfl) sizing reborrow
  have created : RetagPolicy.create ⟨true,true,true⟩ .Mutable .Default ⟨false,false⟩ = some mutablePolicy := by rfl
  have permission := TypedRetagPolicyFields.new_permission_general h place.layout.ty
    .Mutable .Default before frames frame rfl
    unpin unsafeUnpin frozen sources.implicitWrites
  rw [created] at permission
  have construct : h.immPtrToMPlace value = pure place := by
    rw [sources.construct]
    exact Eq.trans (RetagReferencePlace.canonical_from_immediate access prepared choice oldPointer (2 : UInt64) reference
      place.layout dereference pointeeLayout pointeeAlign) (congrArg pure placeShape.symm)
  have changed : TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag =
      RetagReferencePlace.slicePlace newPointer (2 : UInt64) place.layout := by rw [placeShape]; rfl
  have reconstruct : h.reconstruct value (TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag) = pure output := by
    rw [sources.reconstruct, changed]
    exact RetagReferencePlace.bound_reconstruct access h value newPointer (2 : UInt64) place.layout
  have result := TypedBorrowSteps.reference_pointer_of_steps h budget value output place
    (TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag) place.layout.ty .Mut .Default mutablePolicy
    before after shape pointeeQuery permission construct retag reconstruct

  simpa only [before, after, value, output, oldPointer, newPointer, RetagReferencePlace.sliceValue, next] using result
theorem zero_v_pointer_from_fields {K U C F A : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (sources : TypedRetagFields.SourceFields h prepared access projection vtable pointers choice)
    (budget : Nat) (place : MPlaceTy Provenance)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U)) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (base : UInt64) (tree : entry.allocation.extra = b.tree)
    (next : tracker.global.nextPointerTag = tag 5)
    (frozen : h.typeIsFreeze place.layout.ty = pure true)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id (tag 3))) (Size.ofBytes (base + (0 : UInt64))))
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (reference : LocalLayout)
    (shape : h.typeShape reference.ty = pure .reference)
    (pointeeQuery : h.referencePointee reference.ty = pure (place.layout.ty,.Mut))
    (unpin : h.isUnpin place.layout.ty = pure true)
    (unsafeUnpin : h.isUnsafeUnpin place.layout.ty = pure true)
    (dereference : CompilerFacts.builtinDeref prepared.context reference.ty true = .ok (some place.layout.ty))
    (pointeeLayout : CompilerFacts.layoutOf prepared.context place.layout.ty = .ok place.layout)
    (pointeeAlign : place.layout.layout.align.abi = Align.ONE)
    (placeShape : place = RetagReferencePlace.slicePlace
      (Pointer.new (.concrete id (tag 3)) (Size.ofBytes (base+(0 : UInt64)))) (0 : UInt64) place.layout)
    (slice : TypedRetagEntry.SliceFacts projection choice place (0 : UInt64)) :
    TypedRetag.retagPtrValue h budget
      (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id (tag 3)) (Size.ofBytes (base+(0 : UInt64)))) (0 : UInt64) reference)
      reference.ty .Default (Storage.withCurrent frames frame machine) =
      .ok (some (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id (tag 5)) (Size.ofBytes (base+(0 : UInt64)))) (0 : UInt64) reference))
      (Storage.withCurrent frames frame
        {ReferenceBorrowDriver.allocatedMachine machine tracker fresh
          with memory := RetagEntry.updatedMemory machine.memory id entry v.tree}) := by
  have sizing := congrFun (TypedRetagFields.size_from_fields h prepared access projection vtable pointers choice sources place _ slice)
    (Storage.withCurrent frames frame machine)
  let before := Storage.withCurrent frames frame machine
  let after := Storage.withCurrent frames frame
    {ReferenceBorrowDriver.allocatedMachine machine tracker fresh
      with memory := RetagEntry.updatedMemory machine.memory id entry v.tree}
  let oldPointer := Pointer.new (Provenance.concrete id (tag 3)) (Size.ofBytes (base+(0 : UInt64)))
  let newPointer := Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+(0 : UInt64)))
  let value := RetagReferencePlace.sliceValue access.runtime.base oldPointer (0 : UInt64) reference
  let output := RetagReferencePlace.sliceValue access.runtime.base newPointer (0 : UInt64) reference
  have reborrow := zero_v_from_fields h prepared access projection vtable pointers choice sources
    budget place frames frame (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
    (ReferenceBorrowDriver.allocatedTracker tracker fresh) rfl id entry base tree frozen
    pointer width cached globalKind globals extraWiring synchronize present
  have allocatedNext : tracker.global.nextPointerTag = tag 5 := next
  rw [← allocatedNext] at reborrow
  have retag := TypedBorrowSteps.retag_place_at_of_reborrow h budget place mutablePolicy (Size.ofBytes (0 : UInt64)) Align.ONE
    before after tracker enabled fresh id (.concrete id (tag 3)) (by rw [pointer]; rfl) sizing reborrow
  have created : RetagPolicy.create ⟨true,true,true⟩ .Mutable .Default ⟨false,false⟩ = some mutablePolicy := by rfl
  have permission := TypedRetagPolicyFields.new_permission_general h place.layout.ty
    .Mutable .Default before frames frame rfl
    unpin unsafeUnpin frozen sources.implicitWrites
  rw [created] at permission
  have construct : h.immPtrToMPlace value = pure place := by
    rw [sources.construct]
    exact Eq.trans (RetagReferencePlace.canonical_from_immediate access prepared choice oldPointer (0 : UInt64) reference
      place.layout dereference pointeeLayout pointeeAlign) (congrArg pure placeShape.symm)
  have changed : TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag =
      RetagReferencePlace.slicePlace newPointer (0 : UInt64) place.layout := by rw [placeShape]; rfl
  have reconstruct : h.reconstruct value (TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag) = pure output := by
    rw [sources.reconstruct, changed]
    exact RetagReferencePlace.bound_reconstruct access h value newPointer (0 : UInt64) place.layout
  have result := TypedBorrowSteps.reference_pointer_of_steps h budget value output place
    (TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag) place.layout.ty .Mut .Default mutablePolicy
    before after shape pointeeQuery permission construct retag reconstruct

  simpa only [before, after, value, output, oldPointer, newPointer, RetagReferencePlace.sliceValue, next] using result


end DuplicatePrefix.S05ZeroCellCorrelatedTyped

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05ZeroCellCorrelatedTyped." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved correlated typed-prefix dependency {dependency}"
