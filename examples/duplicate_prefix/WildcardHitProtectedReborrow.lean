import duplicate_prefix.WildcardHitAddress
import duplicate_prefix.WildcardHitZeroConstructor
import duplicate_prefix.ConcreteEmptyReferenceBorrow

namespace DuplicatePrefix.WildcardHitProtectedReborrow
open Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Input Miri.Interpreter
open TypedBorrowSteps
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- An actual exposed exact-base live HIT, protected reborrow and concrete
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
    (base : UInt64) (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (tag : BorTag) (policy : RetagPolicy.NewPermission) (initial : Tree.LocationState)
    (protection : policy.protector = some .StrongProtector)
    (frozen : h.typeIsFreeze place.layout.ty = pure true)
    (initialState : RetagPolicy.initialLocationState policy true = .ok initial)
    (pointer : place.mplace.ptr = Pointer.new (some .wildcard) (Size.ofBytes base))
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (mode : machine.user.addresses.provenanceMode ≠ .strict)
    (mapping : machine.user.addresses.intToPtrMap = #[⟨base,id⟩])
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
      .ok (some ⟨id,Size.ofBytes 0,.wildcard⟩) (Storage.withCurrent frames frame machine) := by
    rw [sources.resolve,pointer]
    exact WildcardHitAddress.resolve pointers _ base id entry width mode mapping exposed cached present
  have inside := TypedRetagPolicyFields.inside_for_policy h budget place Size.ZERO policy initial
    initialState sources.precise frozen
  have child := WildcardHitZeroConstructor.append entry.allocation.extra tag fresh noFree fits
    policy.outsidePermission sifa policy.protector.isSome outsideInitial outsideNonunique foreign initial 0
  exact TypedBorrowSteps.protected_live_zero_of_steps h budget place frames frame borrowFrame machine tracker
    enabled frameBorrow id entry 0 .wildcard tag initial policy protection check resolve
    (by rw [sources.log]) inside globalKind globals (sources.ensure.trans extraWiring) synchronize present _ child

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
    (enabled : machine.borrowTracker = some tracker)
    (tagFresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (sizing : h.sizeAndAlign place (Storage.withCurrent frames frame machine) =
      .ok (some (Size.ZERO,Align.ONE)) (Storage.withCurrent frames frame machine))
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (base : UInt64) (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (policy : RetagPolicy.NewPermission) (initial : Tree.LocationState)
    (protection : policy.protector = some .StrongProtector)
    (frozen : h.typeIsFreeze place.layout.ty = pure true)
    (initialState : RetagPolicy.initialLocationState policy true = .ok initial)
    (pointer : place.mplace.ptr = Pointer.new (some .wildcard) (Size.ofBytes base))
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (mode : machine.user.addresses.provenanceMode ≠ .strict)
    (mapping : machine.user.addresses.intToPtrMap = #[⟨base,id⟩])
    (exposed : machine.user.addresses.exposed.contains id = true)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (fresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping tracker.global.nextPointerTag)
    (noFree : entry.allocation.extra.tagMapping.deassigned.back? = none)
    (fits : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (sifa : IdempotentForeignAccess)
    (outsideInitial : policy.outsidePermission.isInitial = true)
    (outsideNonunique : policy.outsidePermission.isUnique = false)
    (foreign : policy.outsidePermission.strongestIdempotentForeignAccess policy.protector.isSome = .Access sifa) :
    let tree := entry.allocation.extra
    let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    let finalTree := WildcardHitZeroConstructor.installed tree
      ⟨tree.tagMapping.mapping.push (tracker.global.nextPointerTag,index),tree.tagMapping.deassigned⟩ index tracker.global.nextPointerTag policy.outsidePermission sifa
    TypedRetag.retagPlace h budget place policy (Storage.withCurrent frames frame machine) =
      .ok (TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag)
        (Storage.withCurrent frames (registeredFrame frame borrowFrame id tracker.global.nextPointerTag)
          { (registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker tagFresh)
              (ReferenceBorrowDriver.allocatedTracker tracker tagFresh) tracker.global.nextPointerTag) with
            memory := RetagEntry.updatedMemory machine.memory id entry finalTree }) := by
  dsimp only
  have reborrow := append h prepared access projection vtable pointers choice sources budget place frames frame borrowFrame
    (ReferenceBorrowDriver.allocatedMachine machine tracker tagFresh)
    (ReferenceBorrowDriver.allocatedTracker tracker tagFresh) rfl frameBorrow base id entry
    tracker.global.nextPointerTag policy initial protection frozen initialState pointer width mode mapping exposed cached present
    globalKind globals extraWiring synchronize fresh noFree fits sifa outsideInitial outsideNonunique foreign
  exact TypedBorrowSteps.retag_place_at_of_reborrow h budget place policy Size.ZERO Align.ONE
    (Storage.withCurrent frames frame machine) _ tracker enabled tagFresh id .wildcard
    (by rw [pointer];rfl) sizing reborrow

end DuplicatePrefix.WildcardHitProtectedReborrow
