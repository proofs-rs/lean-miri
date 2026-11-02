import duplicate_prefix.WildcardOrderedHitAddress
import duplicate_prefix.WildcardHitZeroConstructor
import duplicate_prefix.ConcreteEmptyReferenceBorrow

namespace DuplicatePrefix.WildcardGeneralHitReborrow
open Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Input Miri.Interpreter
open Miri.Memory.AllocAddresses
open TypedBorrowSteps
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Raw finite inverse-vector hit geometry. Exact bases and strictly interior
addresses are distinct source branches; neither clause assumes lookup success. -/
def Geometry (entries : Array InverseAddressEntry) (address base : UInt64) (id : AllocId) (size : Size) : Prop :=
  (address = base ∧ ∃ position, position < entries.size ∧ WildcardInteriorHitAddress.Ordered entries ∧
    entries[position]? = some ⟨base,id⟩) ∨
  ∃ position, WildcardInteriorHitAddress.Cut entries address (position+1) ∧
    entries[position]? = some ⟨base,id⟩ ∧ address-base < size.bytes

/-- Both actual address-search branches yield concrete allocation/relative
position metadata for the unchanged typed resolver. -/
theorem resolve {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (before : ValidityMachine.State K U) (address base : UInt64) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K)
    (geometry : Geometry before.machine.user.addresses.intToPtrMap address base id entry.allocation.byteSize)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (mode : before.machine.user.addresses.provenanceMode ≠ .strict)
    (exposed : before.machine.user.addresses.exposed.contains id = true)
    (cached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : before.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry)) :
    TypedValidityProviders.resolveAllocation pointers (Pointer.new (some .wildcard) (Size.ofBytes address)) before =
      .ok (some ⟨id,Size.ofBytes (address-base),.wildcard⟩) before := by
  rcases geometry with ⟨same,position,valid,ordered,row⟩ | ⟨position,cut,row,inside⟩
  · subst address
    simpa only [UInt64.sub_self,Size.ZERO,Size.ofBytes] using
      WildcardOrderedHitAddress.resolve pointers before base id entry position valid ordered row width mode exposed cached present
  · exact WildcardInteriorHitAddress.resolve pointers before address base id entry position width mode cut row inside exposed cached present

/-- An actual exposed exact-base OR interior live HIT in an arbitrary inverse vector, protected reborrow and concrete
provenance result. All operation successes are derived from source wiring,
physical live/address rows, permission data and fresh append capacity. -/
theorem append {K U C F A : Type} [DecidableEq K]
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
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (address base : UInt64) (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (tag : BorTag) (policy : RetagPolicy.NewPermission) (initial : Tree.LocationState)
    (protection : policy.protector = some .StrongProtector)
    (frozen : h.typeIsFreeze place.layout.ty = pure true)
    (initialState : RetagPolicy.initialLocationState policy true = .ok initial)
    (pointer : place.mplace.ptr = Pointer.new (some .wildcard) (Size.ofBytes address))
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (mode : machine.user.addresses.provenanceMode ≠ .strict)
    (geometry : Geometry machine.user.addresses.intToPtrMap address base id entry.allocation.byteSize)
    (exposed : machine.user.addresses.exposed.contains id = true)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (fresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping tag)
    (noFree : entry.allocation.extra.tagMapping.deassigned.back? = none)
    (fits : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (sifa : IdempotentForeignAccess)
    (outsideInitial : policy.outsidePermission.isInitial = true)
    (outsideNonunique : policy.outsidePermission.isUnique = false)
    (foreign : policy.outsidePermission.strongestIdempotentForeignAccess policy.protector.isSome = .Access sifa) :
    let tree := entry.allocation.extra
    let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    let finalTree := WildcardHitZeroConstructor.installed tree
      ⟨tree.tagMapping.mapping.push (tag,index),tree.tagMapping.deassigned⟩ index tag policy.outsidePermission sifa
    TypedRetag.reborrow h budget place Size.ZERO policy tag (Storage.withCurrent frames frame machine) =
      .ok (some (.concrete id tag))
        (Storage.withCurrent frames (registeredFrame frame borrowFrame id tag)
          { (registeredMachine machine tracker tag) with
            memory := RetagEntry.updatedMemory machine.memory id entry finalTree }) := by
  dsimp only
  have check : h.checkPtrAccess place.mplace.ptr Size.ZERO (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames frame machine) := by
    rw [sources.check]
    exact RetagPointerChecks.check_pointer_zero access place.mplace.ptr _
  have resolve : h.resolveAllocation place.mplace.ptr (Storage.withCurrent frames frame machine) =
      .ok (some ⟨id,Size.ofBytes (address-base),.wildcard⟩) (Storage.withCurrent frames frame machine) := by
    rw [sources.resolve,pointer]
    exact resolve pointers _ address base id entry geometry width mode exposed cached present
  have inside := TypedRetagPolicyFields.inside_for_policy h budget place Size.ZERO policy initial
    initialState sources.precise frozen
  have child := WildcardHitZeroConstructor.append entry.allocation.extra tag fresh noFree fits
    policy.outsidePermission sifa policy.protector.isSome outsideInitial outsideNonunique foreign initial (address-base)
  exact TypedBorrowSteps.protected_live_zero_of_steps h budget place frames frame borrowFrame machine tracker
    enabled frameBorrow id entry (address-base) .wildcard tag initial policy protection check resolve
    (by rw [sources.log]) inside globalKind globals (sources.ensure.trans extraWiring) synchronize present _ child

/-- An actual exposed exact-base OR interior live HIT in an arbitrary inverse vector, protected reborrow and concrete
provenance result. All operation successes are derived from source wiring,
physical live/address rows, permission data and fresh append capacity. -/
theorem reuse {K U C F A : Type} [DecidableEq K]
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
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (address base : UInt64) (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (tag : BorTag) (policy : RetagPolicy.NewPermission) (initial : Tree.LocationState)
    (protection : policy.protector = some .StrongProtector)
    (frozen : h.typeIsFreeze place.layout.ty = pure true)
    (initialState : RetagPolicy.initialLocationState policy true = .ok initial)
    (pointer : place.mplace.ptr = Pointer.new (some .wildcard) (Size.ofBytes address))
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (mode : machine.user.addresses.provenanceMode ≠ .strict)
    (geometry : Geometry machine.user.addresses.intToPtrMap address base id entry.allocation.byteSize)
    (exposed : machine.user.addresses.exposed.contains id = true)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (fresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping tag)
    (index : UniIndex) (available : entry.allocation.extra.tagMapping.deassigned.back? = some index)
    (sifa : IdempotentForeignAccess)
    (outsideInitial : policy.outsidePermission.isInitial = true)
    (outsideNonunique : policy.outsidePermission.isUnique = false)
    (foreign : policy.outsidePermission.strongestIdempotentForeignAccess policy.protector.isSome = .Access sifa) :
    let tree := entry.allocation.extra
    let finalTree := WildcardHitZeroConstructor.installed tree
      ⟨tree.tagMapping.mapping.push (tag,index),tree.tagMapping.deassigned.pop⟩ index tag policy.outsidePermission sifa
    TypedRetag.reborrow h budget place Size.ZERO policy tag (Storage.withCurrent frames frame machine) =
      .ok (some (.concrete id tag))
        (Storage.withCurrent frames (registeredFrame frame borrowFrame id tag)
          { (registeredMachine machine tracker tag) with
            memory := RetagEntry.updatedMemory machine.memory id entry finalTree }) := by
  dsimp only
  have check : h.checkPtrAccess place.mplace.ptr Size.ZERO (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames frame machine) := by
    rw [sources.check]
    exact RetagPointerChecks.check_pointer_zero access place.mplace.ptr _
  have resolve : h.resolveAllocation place.mplace.ptr (Storage.withCurrent frames frame machine) =
      .ok (some ⟨id,Size.ofBytes (address-base),.wildcard⟩) (Storage.withCurrent frames frame machine) := by
    rw [sources.resolve,pointer]
    exact resolve pointers _ address base id entry geometry width mode exposed cached present
  have inside := TypedRetagPolicyFields.inside_for_policy h budget place Size.ZERO policy initial
    initialState sources.precise frozen
  have child := WildcardHitZeroConstructor.reuse entry.allocation.extra tag index fresh available
    policy.outsidePermission sifa policy.protector.isSome outsideInitial outsideNonunique foreign initial (address-base)
  exact TypedBorrowSteps.protected_live_zero_of_steps h budget place frames frame borrowFrame machine tracker
    enabled frameBorrow id entry (address-base) .wildcard tag initial policy protection check resolve
    (by rw [sources.log]) inside globalKind globals (sources.ensure.trans extraWiring) synchronize present _ child

end DuplicatePrefix.WildcardGeneralHitReborrow
