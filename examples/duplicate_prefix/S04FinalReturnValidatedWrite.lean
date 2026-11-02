import duplicate_prefix.S04FinalReturnWrite
import duplicate_prefix.S04ReturnAllocationClear
import duplicate_prefix.S04ReturnActualBoolValidity
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.S04FinalReturnValidatedWrite
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Input
open DuplicatePrefixCallSpecification
set_option autoImplicit false
/-- Final concrete destination store followed by the actual Shallow validation,
from current local runtime and byte metadata. The compiler write policy and
second provenance-clear mutation are preserved. No whole-state Resources,
Model or successful validation operation is assumed. -/
theorem from_current {options : EvalConfigurationCore.Options}
    {remaining : Nat} (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance)
    (input : DuplicatePrefixReturnPlaceInput.Input state.machine place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global)
    (distinct : input.entry.allocation.extra.roots.toList.Nodup)
    (order : ∀ valid : 0 < input.entry.allocation.extra.roots.size,
      ∀ selected, input.selectedRoot = some selected → selected ≠ input.entry.allocation.extra.roots[0] →
        GeneralBorrowWildcardParentTagOrder.ParentTagOrder input.entry.allocation.extra)
    (short : input.entry.allocation.extra.nodes.size < 65536)
    (tag : BorTag) (concrete : input.pointer.provenance = .concrete input.id tag)
    (race : state.machine.dataRace = none)
    (backend : state.machine.user.payload.payload.user.backend = .none)
    (ghost : state.machine.user.payload.ghost = false)
    (shallow : state.machine.user.payload.validation = .Shallow)
    (sync : Array (Size × MemoryExtras.Entry Unit))
    (extras : state.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == input.id) =
      some (input.id,⟨none,sync⟩))
    (outside : ∀ row ∈ sync,
      row.1.bytes.toNat < input.offset.toNat ∨ input.offset.toNat + 1 ≤ row.1.bytes.toNat)
    (value : Bool) (fuel : Nat) :
    let outer := PreparedContracts.actualConfig options () (remaining+1) span
    let inner := PreparedContracts.actualConfig options () remaining span
    let tree := (input.entry.allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes input.offset) (Size.ofBytes 1) .Write input.tracker.global.protectedTags
      .VisitChildrenOfAccessed).tree
    ∃ updated, (do
      PlaceMachine.writeMemory outer.access outer.compiler.willValidateMemory (.scalar (Scalar.fromBool value)) place
      ValidityMachine.validateRuntime inner.validity () (fuel+1) ⟨.memory place.mplace,place.layout⟩ true) state =
      .ok () (CanonicalCopy.replaceAllocation state input.id input.entry.kind updated) ∧
      updated.extra = tree ∧ updated.byteSize = input.entry.allocation.byteSize ∧
      updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut := by
  let contexts := DuplicatePrefixPhysicalContexts.canonical options remaining span
  let context := contexts.validationContext
  obtain ⟨stored,write,writeTree,writeSize,writeLen,writeMut,read,pointerBounds,_⟩ :=
    S04FinalReturnWrite.from_current (options := options) (remaining := remaining) span state place input
      runtime distinct order short tag concrete race backend sync extras outside value
  let after := CanonicalCopy.replaceAllocation state input.id input.entry.kind stored
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind := ⟨input.entry.kind,stored⟩
  have present : after.machine.memory.live.find? (fun row => row.1 == input.id) = some (input.id,entry) :=
    CanonicalCopy.replace_lookup state input.id input.entry.kind stored
  have size : stored.byteSize = Size.ofBytes input.capacity := writeSize.trans input.size
  have storage : stored.len = input.capacity.toNat := writeLen.trans input.bytes
  obtain ⟨updated,mutation,clearLen,clearSize,clearMut,clearExtra,clearMask,clearRead⟩ :=
    S04ReturnAllocationClear.clear_exists stored input.capacity input.offset storage size input.bounds pointerBounds
  let active := S04ReturnBoolValidation.ghostState after
  let provenance := S04ReturnBorrowBridge.extra input.pointer.provenance
  have cached : active.machine.user.addresses.baseAddr.find? (fun row => row.allocId == input.id) =
      some ⟨input.id,input.base⟩ := input.cachedBase
  have activePresent : active.machine.memory.live.find? (fun row => row.1 == input.id) = some (input.id,entry) := present
  have off : input.pointer.offset = Size.ofBytes (input.base+input.offset) := by
    cases h : input.pointer.offset
    simpa [h,Size.ofBytes] using congrArg Size.ofBytes input.pointerAddress
  have pointer : place.mplace.ptr = Pointer.new (some input.pointer.provenance) (Size.ofBytes (input.base+input.offset)) := by
    rw [input.physicalPointer]
    simp only [Pointer.withOptionalProvenance,Pointer.new,off]
  have resolved : context.access.resolvePointer active.machine.memory
      (Pointer.new (some input.pointer.provenance) (Size.ofBytes (input.base+input.offset)))
      (Int.ofNat (1 : UInt64).toNat) active.machine =
      .ok (.ok ⟨input.id,Size.ofBytes input.offset,provenance⟩) active.machine := by
    rw [show context.access.resolvePointer = TypedMemoryProviders.resolvePointer context.pointers from rfl]
    have res := MemoryCopyBridge.typed_resolve_cached context.pointers active.machine.memory active.machine
      input.id tag input.base input.offset (Int.ofNat (1 : UInt64).toNat) contexts.validationWidth
      (by decide) (by decide) cached
    simpa only [concrete,provenance,S04ReturnBorrowBridge.extra] using res
  have read' : Allocation.readScalar stored context.access.runtime.base
      (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) false = .ok (Scalar.fromBool value) := by
    rw [contexts.sameRuntime]
    rw [←contexts.outerAccessEq]
    exact read
  have addressBound : place.mplace.ptr.offset.bytes.toNat+1<2^64 := by
    rw [input.physicalPointer]
    change input.pointer.offset.bytes.toNat+1<2^64
    have interval := input.address_interval
    have fits := input.addressFits
    omega
  have endpoint := DuplicatePrefix.source_end place.mplace.ptr.offset 1
    (by simpa using addressBound)
  have validation := S04ReturnActualBoolValidity.validate_actual context options remaining span contexts.accessEq
    after place.mplace input.id input.pointer.provenance provenance input.base input.offset input.capacity entry updated value fuel
    contexts.validationWidth input.cachedBase present size input.bounds writeMut read' mutation pointer input.aligned
    contexts.validationRuntimeSize resolved ghost shallow _ endpoint
  have memoryEq : CanonicalCopy.replaceAllocation after input.id entry.kind updated =
      CanonicalCopy.replaceAllocation state input.id input.entry.kind updated := by
    unfold after CanonicalCopy.replaceAllocation
    simp [entry,Array.filter_filter]
  rw [memoryEq] at validation
  refine ⟨updated,?_,clearExtra.trans writeTree,clearSize.trans writeSize,clearLen.trans writeLen,clearMut.trans writeMut⟩
  rw [input.layout]
  simp only [Bind.bind,EStateM.bind]
  erw [write]
  exact validation
end DuplicatePrefix.S04FinalReturnValidatedWrite
