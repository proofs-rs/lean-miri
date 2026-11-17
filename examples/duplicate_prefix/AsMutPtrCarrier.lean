import duplicate_prefix.ActualRootReferenceDeref
import duplicate_prefix.ActualReferenceMetadata
import duplicate_prefix.SliceLenRawPlace
import duplicate_prefix.SliceLenRawRvalue
namespace DuplicatePrefix.AsMutPtrCarrier
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts PtrMetadataHelper PtrMetadataComplete SliceLenRawRvalue
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Structural shared-slice pointer geometry, before executing any MIR action.
Zero-length references need no allocation or provenance liveness fact. -/
inductive Valid (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
    (Pointer Provenance ⊕ UInt64) → UInt64 → Prop
  | positive (id : AllocId) (tag : BorTag) (base offset len : UInt64)
      (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
      (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
      (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
      (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
      (signedFits : len.toNat < 9223372036854775808)
      (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat) :
      Valid machine (.inl (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset)))) len
  | zeroPointer (pointer : Pointer Provenance) (nonzero : pointer.offset.bytes ≠ 0) : Valid machine (.inl pointer) 0
  | zeroInteger (address : UInt64) (nonzero : address ≠ 0) : Valid machine (.inr address) 0

theorem actual_dereference
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (state : RootState) (carrier : Pointer Provenance ⊕ UInt64) (len : UInt64)
    (valid : Valid state.machine carrier len)
    (fuel : Nat) (fuelEq : options.place.dynamicFuel = fuel+1)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get state).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get state).entries.any (·.value.ty == 4) = false) :
    let config := PreparedContracts.actualConfig options () remaining span
    config.operands.dereference ()
      ⟨.immediate (rawImmediate carrier config.access.runtime.base len),ActualReferenceMetadata.reference⟩ state =
      .ok ⟨carrierMemory carrier len,ProjectionMetadataFacts.sliceLayout⟩ state := by
  cases valid with
  | positive id tag base offset len entry cached present positive nonzero signedFits bounds =>
    exact ActualRootReferenceDeref.actual_positive_dereference options remaining span state id tag base offset len entry
      cached present positive nonzero signedFits bounds fuel fuelEq cmp metadata notConstructed
  | zeroPointer pointer nonzero =>
    exact ActualRootReferenceDeref.actual_zero_dereference options remaining span state pointer nonzero
      fuel fuelEq cmp metadata notConstructed
  | zeroInteger address nonzero =>
    exact ActualRootReferenceDeref.actual_integer_zero_dereference options remaining span state address nonzero
      fuel fuelEq cmp metadata notConstructed

theorem actual_eval_deref
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (carrier : Pointer Provenance ⊕ UInt64) (len : UInt64)
    (valid : Valid machine carrier len)
    (valid1 : (1 : Miri.MIR.LocalId) < frame.locals.size)
    (live1 : frame.locals[1].value = .live (.immediate
      (rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len)))
    (cached1 : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (noClocks : frame.extra.dataRace = none) (ghost : machine.user.payload.ghost = false)
    (fuel : Nat) (fuelEq : options.place.dynamicFuel = fuel+1)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits).evalPlace ()
      ⟨1,#[.Deref]⟩ false (Storage.withCurrent frames frame machine) =
      .ok ⟨.memory (carrierMemory carrier len),ProjectionMetadataFacts.sliceLayout⟩
        (Storage.withCurrent frames frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let value := rawImmediate carrier config.access.runtime.base len
  have staged := SliceLenRawPlace.actual_eval_deref_cached_local options limits remaining span debugOff frames frame machine
    1 value ActualReferenceMetadata.reference valid1 live1 cached1 ActualReferenceMetadata.reference_sized noClocks ghost
  rw [staged]
  have result := actual_dereference options remaining span (Storage.withCurrent frames frame machine) carrier len
    valid fuel fuelEq cmp metadata notConstructed
  have result' : config.operands.dereference () ⟨.immediate value,ActualReferenceMetadata.reference⟩
      (Storage.withCurrent frames frame machine) =
      .ok ⟨carrierMemory carrier len,ProjectionMetadataFacts.sliceLayout⟩ (Storage.withCurrent frames frame machine) := result
  simp only [bind,EStateM.bind]
  rw [result']
  rfl

#print axioms actual_eval_deref
end
end DuplicatePrefix.AsMutPtrCarrier
