import duplicate_prefix.ExecutionStackRootAddressResources
import duplicate_prefix.CandidateCallBindings
import duplicate_prefix.CanonicalConfigFacts
import duplicate_prefix.PointerArithmetic

namespace DuplicatePrefix.CurrentCallPointerFormation
open Miri Miri.Input Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts GlobalAddressAlignedBumpFormation
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- The actual managed stack-root pointer producer establishes its selected
post-state binding, including interior offsets. The cache is formed by address
assignment rather than required of the initial state. This covers the stack
producer only, not extern statics or arbitrary ordinary reference origins. -/
theorem stack_binding (pointers : RootPointers) (extras : RootExtras)
    (config : PlaceMachine.AllocationConfig MiriMemoryKind Machine.RootUser)
    (before : RootState) (generation : AddressGenerationState) (sizes : AllocId → Size)
    (initial : GlobalAddressReuseResources.State before.machine.memory before.machine.user.addresses generation sizes)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tag : BorTag)
    (present : before.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (stack : entry.kind = .stack) (sizeEq : sizes id = entry.allocation.byteSize)
    (uncached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (valid : entry.allocation.align.pow2 ≤ 29) (slack : Fin 16)
    (supplied : (EvalAllocationMachine.tape.get before).inputs[(EvalAllocationMachine.tape.get before).cursor]? =
      some (.index .addressSlack slack.val))
    (room : Room generation.generator entry.allocation.byteSize entry.allocation.align slack)
    (extent : entry.allocation.len = entry.allocation.byteSize.bytes.toNat)
    (offset : UInt64) (length : Nat) (bounds : offset.toNat+length ≤ entry.allocation.len) :
    let address := base generation.generator entry.allocation.align slack
    let final := ManagedStackPointerFormation.after (ExecutionStackRootAddressFormation.chosen before slack)
      generation entry.allocation.byteSize entry.allocation.align id slack
    (EvalAllocationMachine.allocation pointers extras config).adjustRootAddress id tag before =
      .ok (Pointer.new (Provenance.concrete id tag) (Size.ofBytes address)) final ∧
      (Pointer.new (Provenance.concrete id tag) (Size.ofBytes address)).wrappingOffset (Size.ofBytes offset) ⟨Size.ofBytes 8⟩ =
        .ok (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (address+offset))) ∧
      CandidateCallBindings.WindowBinding final.machine
        (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (address+offset))) id offset.toNat length := by
  dsimp only
  let address := base generation.generator entry.allocation.align slack
  let final := ManagedStackPointerFormation.after (ExecutionStackRootAddressFormation.chosen before slack)
    generation entry.allocation.byteSize entry.allocation.align id slack
  have assigned := ExecutionStackRootAddressFormation.address pointers before generation sizes initial id entry present sizeEq
    uncached valid slack supplied room
  have selectedLive : ((before.machine.memory.live.map fun (id,entry) => (id,entry.kind,entry.allocation)).find?
      (fun row => row.1 == id)) = some (id,.stack,entry.allocation) := by
    rw [Array.find?_map]
    change (before.machine.memory.live.find? (fun row => row.1 == id)).map (fun row => (row.1,row.2.kind,row.2.allocation)) = _
    simp only [present,Option.map_some,stack]
  have actual : (EvalAllocationMachine.allocation pointers extras config).adjustRootAddress id tag before =
      .ok (Pointer.new (Provenance.concrete id tag) (Size.ofBytes address)) final := by
    unfold EvalAllocationMachine.allocation
    unfold_internal ".EvalAllocationMachine.addressKind"
    simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,selectedLive]
    rw [assigned]
  have cached := ExecutionStackRootAddressResources.cached
    (GlobalAddressStackManagedFormation.ready before.machine.user.addresses generation entry.allocation.byteSize entry.allocation.align slack)
    id address uncached
  have finalCached : final.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,address⟩ := cached
  have finalLive : final.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry) := present
  have baseBounds := base_bounds generation.generator entry.allocation.byteSize entry.allocation.align valid slack room
  have capacity : address.toNat+entry.allocation.len < 2^64 := by
    have headroom := room.1
    rw [GlobalAddressBumpRangeFormation.length_nat] at headroom
    dsimp only [address]
    rw [extent]
    omega
  have offsetNat : (address+offset).toNat = address.toNat+offset.toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt]
    omega
  have nonnull : address+offset ≠ 0 := by
    intro zero
    have cursor : generation.generator.nextBaseAddr.toNat ≠ 0 := by
      intro same
      exact initial.cursor (UInt64.toNat_inj.mp same)
    have pointerNat := offsetNat
    rw [zero] at pointerNat
    change (0 : Nat) = address.toNat+offset.toNat at pointerNat
    dsimp only [address] at pointerNat
    omega
  refine ⟨actual,?_,?_⟩
  · exact DuplicatePrefix.PointerArithmetic.wrapping_offset_u64 _ _
  · exact ⟨entry,address,finalLive,finalCached,extent,capacity,bounds,offsetNat,nonnull,rfl⟩

end DuplicatePrefix.CurrentCallPointerFormation

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallPointerFormation" then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved pointer formation dependency {dependency}"
