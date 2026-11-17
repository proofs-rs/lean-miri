import duplicate_prefix.WildcardGeneralHitReborrow
import duplicate_prefix.WildcardHitPoolRoot

namespace DuplicatePrefix.WildcardPoolHitReborrow
open Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Input Miri.Interpreter
open Miri.TreeBorrows.Tree
open TypedBorrowSteps
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
attribute [local irreducible] UniValMap.insert

def after (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (outside : Permission) (sifa : IdempotentForeignAccess) : BorrowTree :=
  WildcardHitZeroConstructor.installed tree (slot.mapping tag) slot.index tag outside sifa

/-- An actual exposed exact-base OR interior live HIT in an arbitrary inverse vector, protected reborrow and concrete
provenance result. All operation successes are derived from source wiring,
physical live/address rows, permission data and the real append/reuse Slot. -/
theorem run {K U C F A : Type} [DecidableEq K]
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
    (geometry : WildcardGeneralHitReborrow.Geometry machine.user.addresses.intToPtrMap address base id entry.allocation.byteSize)
    (exposed : machine.user.addresses.exposed.contains id = true)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (fresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping tag)
    (slot : WildcardHitPoolRoot.Slot entry.allocation.extra)
    (sifa : IdempotentForeignAccess)
    (outsideInitial : policy.outsidePermission.isInitial = true)
    (outsideNonunique : policy.outsidePermission.isUnique = false)
    (foreign : policy.outsidePermission.strongestIdempotentForeignAccess policy.protector.isSome = .Access sifa) :
    let finalTree := after entry.allocation.extra slot tag policy.outsidePermission sifa
    TypedRetag.reborrow h budget place Size.ZERO policy tag (Storage.withCurrent frames frame machine) =
      .ok (some (.concrete id tag))
        (Storage.withCurrent frames (registeredFrame frame borrowFrame id tag)
          { (registeredMachine machine tracker tag) with
            memory := RetagEntry.updatedMemory machine.memory id entry finalTree }) := by
  dsimp only
  cases slot with
  | append noFree _aligned fits =>
    exact WildcardGeneralHitReborrow.append h prepared access projection vtable pointers choice sources budget place frames frame borrowFrame
      machine tracker enabled frameBorrow address base id entry tag policy initial protection frozen initialState pointer width mode geometry
      exposed cached present globalKind globals extraWiring synchronize fresh noFree fits sifa outsideInitial outsideNonunique foreign
  | reuse index available _bounded _vacant =>
    exact WildcardGeneralHitReborrow.reuse h prepared access projection vtable pointers choice sources budget place frames frame borrowFrame
      machine tracker enabled frameBorrow address base id entry tag policy initial protection frozen initialState pointer width mode geometry
      exposed cached present globalKind globals extraWiring synchronize fresh index available sifa outsideInitial outsideNonunique foreign

end DuplicatePrefix.WildcardPoolHitReborrow
