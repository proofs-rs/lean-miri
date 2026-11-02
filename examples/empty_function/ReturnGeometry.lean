import empty_function.FootprintAfter
import empty_function.ProjectionSnapshot
import empty_function.ProjectedIndirectCopy
import empty_function.OrdinaryReturnNoUB

namespace EmptyFunction.ReturnGeometry
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.Configuration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Positive offset uses the original parent footprint and the actual source
address extension. Zero offset consults neither parent bounds nor tables. -/
theorem inbounds (s : Static) (metadata : Metadata s) (before after : State)
    (place : MemPlace Provenance) (length amount : Size)
    (footprint : length.bytes ≠ 0 → Nonempty (InputDraft.IndirectFootprint before place.ptr length))
    (within : amount.bytes.toNat ≤ length.bytes.toNat) (signed : length.bytes.toNat < 2^63)
    (posts : amount.bytes ≠ 0 → Preservation.OriginalLiveAllocations before after ∧
      Preservation.ExistingAddressFacts before after ∧ FootprintAfter.Geometry before after) :
    EvalProjectionMachine.memoryOffset (ConcreteProtection.source s).pointers after place amount .inbounds .none =
      .ok (ProjectedIndirectPreflight.shifted place amount) := by
  by_cases zero : amount.bytes = 0
  · have same : amount = Size.ZERO := by cases amount; cases zero; rfl
    rw [same]
    have zeroQuery := ProjectionZero.source s metadata after place
    simpa [ProjectedIndirectPreflight.shifted,Size.ZERO,Size.ofBytes] using zeroQuery
  · have parentPositive : length.bytes ≠ 0 := by
      intro empty
      have positive : 0 < amount.bytes.toNat := by
        have different : amount.bytes.toNat ≠ 0 := by intro equal;apply zero;exact UInt64.toNat_inj.mp equal
        omega
      rw [empty] at within
      simp only [UInt64.toNat_zero] at within
      omega
    obtain ⟨foot⟩ := footprint parentPositive
    obtain ⟨physical,addresses,geometry⟩ := posts zero
    exact FootprintAfter.offset s metadata before after place length amount foot zero within signed physical addresses geometry

/-- Metadata/address-only observation survives child insertion, real protector
release, frame-pop relevance updates and ghost validation scopes. -/
theorem inbounds_after_snapshot (s : Static) (metadata : Metadata s)
    (before geometryAt after : State) (place : MemPlace Provenance) (length amount : Size)
    (footprint : length.bytes ≠ 0 → Nonempty (InputDraft.IndirectFootprint before place.ptr length))
    (within : amount.bytes.toNat ≤ length.bytes.toNat) (signed : length.bytes.toNat < 2^63)
    (posts : amount.bytes ≠ 0 → Preservation.OriginalLiveAllocations before geometryAt ∧
      Preservation.ExistingAddressFacts before geometryAt ∧ FootprintAfter.Geometry before geometryAt)
    (addresses : after.machine.user.addresses = geometryAt.machine.user.addresses)
    (info : ∀ id, after.machine.memory.getAllocInfo id = geometryAt.machine.memory.getAllocInfo id)
    (live : ∀ id, after.machine.memory.isAllocLive id = geometryAt.machine.memory.isAllocLive id) :
    EvalProjectionMachine.memoryOffset (ConcreteProtection.source s).pointers after place amount .inbounds .none =
      .ok (ProjectedIndirectPreflight.shifted place amount) := by
  rw [ProjectionSnapshot.offset_congr (ConcreteProtection.source s).pointers geometryAt after addresses info live]
  exact inbounds s metadata before geometryAt place length amount footprint within signed posts

theorem destination_query (s : Static) (metadata : Metadata s)
    (p : Packet) (tracker : MachineHooks.BorrowState) (destination : InputDraft.LocalDestination s p tracker)
    (amount : Size) (projected : destination.offset = some amount)
    (memory : MemPlace Provenance) (indirect : destination.oldOperand = .indirect memory) (after : State)
    (posts : amount.bytes ≠ 0 → Preservation.OriginalLiveAllocations p.before after ∧
      Preservation.ExistingAddressFacts p.before after ∧ FootprintAfter.Geometry p.before after) :
    EvalProjectionMachine.memoryOffset (ConcreteProtection.source s).pointers after memory amount .inbounds .none =
      .ok (ProjectedIndirectPreflight.shifted memory amount) := by
  have footprint : destination.baseLayout.layout.size.bytes ≠ 0 →
      Nonempty (InputDraft.IndirectFootprint p.before memory.ptr destination.baseLayout.layout.size) := by
    intro positive
    exact destination.oldFootprint (by rw [projected];rfl) positive memory indirect
  have within : amount.bytes.toNat ≤ destination.baseLayout.layout.size.bytes.toNat := by
    cases destination
    cases projected
    assumption
  exact inbounds s metadata p.before after memory destination.baseLayout.layout.size amount
    footprint within destination.baseSigned posts

/-- Internal actual inbounds-query composition, discharged by destination_query
or its metadata-snapshot transport below. -/
theorem copy_of_query (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2) (validation : 0 < s.options.limits.validation)
    (p : Packet) (tracker : MachineHooks.BorrowState) (destination : InputDraft.LocalDestination s p tracker)
    (amount : Size) (projected : destination.offset = some amount)
    (memory : MemPlace Provenance) (indirect : destination.oldOperand = .indirect memory)
    (older : Array LocalUnit.F) (caller callee : LocalUnit.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (slotAt : caller.locals[destination.localId]? = some {destination.slot with layout := some destination.baseLayout})
    (noClocks : caller.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (returnPlace : callee.returnPlace =
      .frameLocal older.size destination.localId (some amount) s.abi.ret.layout caller.localsIdentity)
    (sourceQuery : EvalProjectionMachine.memoryOffset (ConcreteProtection.source s).pointers
      (LocalUnit.current older caller machine) memory amount .inbounds .none =
      .ok (ProjectedIndirectPreflight.shifted memory amount)) :
    (ReturnStep.control s).copyReturn () ⟨.immediate .uninit,s.abi.ret.layout⟩ callee.returnPlace
      (LocalUnit.current older caller machine) = (LocalUnit.current older caller machine,.ok ()) := by
  have activeQuery : EvalProjectionMachine.memoryOffset (ConcreteProtection.source s).pointers
      (BodyValidation.active (LocalUnit.current older caller machine)) memory amount .inbounds .none =
      .ok (ProjectedIndirectPreflight.shifted memory amount) := by
    rw [ProjectionSnapshot.offset_congr (ConcreteProtection.source s).pointers
      (LocalUnit.current older caller machine) (BodyValidation.active (LocalUnit.current older caller machine))
      rfl (fun _ => rfl) (fun _ => rfl)]
    exact sourceQuery
  have value : ({destination.slot with layout := some destination.baseLayout} : LocalState Provenance LocalLayout).value =
      .live (.indirect memory) := by rw [destination.live,indirect]
  have representation := destination.oldRepresentation memory indirect
  rw [returnPlace]
  exact ProjectedIndirectCopy.control_copy s metadata profile remaining capacity validation older caller machine
    destination.localId {destination.slot with layout := some destination.baseLayout} destination.baseLayout memory amount
    slotAt value rfl noClocks representation.2 noGhost shallow activeQuery

/-- The complete copy wrapper derives its query from original raw footprint;
positive offsets alone require geometry preservation. -/
theorem copy (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2) (validation : 0 < s.options.limits.validation)
    (p : Packet) (tracker : MachineHooks.BorrowState) (destination : InputDraft.LocalDestination s p tracker)
    (amount : Size) (projected : destination.offset = some amount)
    (memory : MemPlace Provenance) (indirect : destination.oldOperand = .indirect memory)
    (older : Array LocalUnit.F) (caller callee : LocalUnit.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (slotAt : caller.locals[destination.localId]? = some {destination.slot with layout := some destination.baseLayout})
    (noClocks : caller.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (returnPlace : callee.returnPlace =
      .frameLocal older.size destination.localId (some amount) s.abi.ret.layout caller.localsIdentity)
    (posts : amount.bytes ≠ 0 →
      Preservation.OriginalLiveAllocations p.before (LocalUnit.current older caller machine) ∧
      Preservation.ExistingAddressFacts p.before (LocalUnit.current older caller machine) ∧
      FootprintAfter.Geometry p.before (LocalUnit.current older caller machine)) :
    (ReturnStep.control s).copyReturn () ⟨.immediate .uninit,s.abi.ret.layout⟩ callee.returnPlace
      (LocalUnit.current older caller machine) = (LocalUnit.current older caller machine,.ok ()) := by
  have query := destination_query s metadata p tracker destination amount projected memory indirect
    (LocalUnit.current older caller machine) posts
  exact copy_of_query s metadata profile remaining capacity validation p tracker destination amount projected
    memory indirect older caller callee machine slotAt noClocks noGhost shallow returnPlace query

 theorem copy_outcome (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2) (validation : 0 < s.options.limits.validation)
    (p : Packet) (tracker : MachineHooks.BorrowState) (destination : InputDraft.LocalDestination s p tracker)
    (amount : Size) (projected : destination.offset = some amount)
    (memory : MemPlace Provenance) (indirect : destination.oldOperand = .indirect memory)
    (older : Array LocalUnit.F) (caller callee : LocalUnit.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (slotAt : caller.locals[destination.localId]? = some {destination.slot with layout := some destination.baseLayout})
    (noClocks : caller.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (returnPlace : callee.returnPlace =
      .frameLocal older.size destination.localId (some amount) s.abi.ret.layout caller.localsIdentity)
    (posts : amount.bytes ≠ 0 →
      Preservation.OriginalLiveAllocations p.before (LocalUnit.current older caller machine) ∧
      Preservation.ExistingAddressFacts p.before (LocalUnit.current older caller machine) ∧
      FootprintAfter.Geometry p.before (LocalUnit.current older caller machine)) :
    OrdinaryReturnNoUB.CopyOutcome s older caller callee machine := by
  exact Or.inr ⟨caller,machine,copy s metadata profile remaining capacity validation p tracker destination amount projected
    memory indirect older caller callee machine slotAt noClocks noGhost shallow returnPlace posts⟩

theorem outcome_after_snapshot (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2) (validation : 0 < s.options.limits.validation)
    (p : Packet) (tracker : MachineHooks.BorrowState) (destination : InputDraft.LocalDestination s p tracker)
    (amount : Size) (projected : destination.offset = some amount)
    (memory : MemPlace Provenance) (indirect : destination.oldOperand = .indirect memory)
    (older : Array LocalUnit.F) (caller callee : LocalUnit.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (slotAt : caller.locals[destination.localId]? = some {destination.slot with layout := some destination.baseLayout})
    (noClocks : caller.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (returnPlace : callee.returnPlace =
      .frameLocal older.size destination.localId (some amount) s.abi.ret.layout caller.localsIdentity)
    (geometryAt : State)
    (posts : amount.bytes ≠ 0 → Preservation.OriginalLiveAllocations p.before geometryAt ∧
      Preservation.ExistingAddressFacts p.before geometryAt ∧ FootprintAfter.Geometry p.before geometryAt)
    (addresses : machine.user.addresses = geometryAt.machine.user.addresses)
    (info : ∀ id, machine.memory.getAllocInfo id = geometryAt.machine.memory.getAllocInfo id)
    (live : ∀ id, machine.memory.isAllocLive id = geometryAt.machine.memory.isAllocLive id) :
    OrdinaryReturnNoUB.CopyOutcome s older caller callee machine := by
  have query : EvalProjectionMachine.memoryOffset (ConcreteProtection.source s).pointers
      (LocalUnit.current older caller machine) memory amount .inbounds .none =
      .ok (ProjectedIndirectPreflight.shifted memory amount) := by
    rw [ProjectionSnapshot.offset_congr (ConcreteProtection.source s).pointers geometryAt
      (LocalUnit.current older caller machine) addresses info live]
    exact destination_query s metadata p tracker destination amount projected memory indirect geometryAt posts
  exact Or.inr ⟨caller,machine,copy_of_query s metadata profile remaining capacity validation p tracker destination
    amount projected memory indirect older caller callee machine slotAt noClocks noGhost shallow returnPlace query⟩

open Lean Elab Command in
run_cmd do
  let mut total : Nat := 0
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.ReturnGeometry." ||
        (name.toString.startsWith "_private." && name.toString.contains "ReturnGeometry") then
      total := total+1
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved return geometry axiom {dependency} in {name}"
  logInfo m!"Audited {total} actual Return geometry declarations"
#print axioms copy_outcome
#print axioms outcome_after_snapshot
end EmptyFunction.ReturnGeometry
