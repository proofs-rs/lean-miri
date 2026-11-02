import duplicate_prefix.RootOffsetQueries
import duplicate_prefix.ExecutionPointerOffset
import duplicate_prefix.CopyCompilerFacts
namespace DuplicatePrefix.ActualOffset
open Miri Miri.ABI Miri.Input Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem pointee_query (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) :
    (PreparedContracts.actualConfig options () remaining span).pointeeLayout ()
      CopyCompilerFacts.destPointerLayout.ty = pure CopyCompilerFacts.byteLayout := by
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).pointeeLayout]
  have ty : CopyCompilerFacts.destPointerLayout.ty = 8 := by decide +kernel
  rw [ty]
  exact CanonicalConfigFacts.pointee_query_supported _ 8 1 _
    RootMetadataQueries.destination_pointer_pointee CopyCompilerFacts.compiler_byte_layout

theorem destination_classification (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) :
    (PreparedContracts.actualConfig options () remaining span).scalar.classify ()
      CopyCompilerFacts.destPointerLayout.ty = pure .pointer := by
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).scalar]
  unfold_scalar_leaves
  have ty : CopyCompilerFacts.destPointerLayout.ty = 8 := by decide +kernel
  rw [ty]
  have query := RootOffsetQueries.destination_classification
  simp only [RootMetadataQueries.context] at query
  rw [query]

/-- The production scalar Offset operation on a live cached byte pointer. -/
theorem byte_offset
    (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (id : AllocId) (tag : BorTag) (base offset count : UInt64)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (positive : 0 < count.toNat) (fits : count.toNat < 2^63)
    (bounds : offset.toNat + count.toNat ≤ entry.allocation.byteSize.bytes.toNat) :
    ScalarOps.binary (ExecutionMachine.scalarHooks (PreparedContracts.actualConfig options () remaining span))
      () .Offset
      (PointerDispatch.pointerImmediate (PreparedContracts.actualConfig options () remaining span).access.runtime.base
        (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset))) CopyCompilerFacts.destPointerLayout)
      (ScalarOperations.usizeImmediate count RootCompilerFacts.usizeLayout) state =
    .ok (PointerDispatch.pointerImmediate (PreparedContracts.actualConfig options () remaining span).access.runtime.base
      (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset+count))) CopyCompilerFacts.destPointerLayout) state := by
  let config := PreparedContracts.actualConfig options () remaining span
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have lhs := destination_classification options remaining span
  have rhs : config.scalar.classify () RootCompilerFacts.usizeLayout.ty = pure (.integer .usize) := by
    rw [fields.scalar]
    unfold_scalar_leaves
    have ty : RootCompilerFacts.usizeLayout.ty = 5 := by decide +kernel
    rw [ty]
    have query := RootMetadataQueries.usize_classification
    simp only [RootMetadataQueries.context] at query
    rw [query]
  rw [ExecutionPointerOffset.scalar_binary_pointer _ () .Offset _ _ lhs rhs]
  obtain ⟨pointers, arithmeticSource, resolution⟩ := fields.pointerSource
  have arithmetic := CanonicalConfigFacts.actual_arithmetic options () remaining span
  have pointerWidth : pointers.arithmetic = ⟨Size.ofBytes 8⟩ := arithmeticSource.symm.trans arithmetic
  exact ExecutionPointerOffset.pointer_binary_cached config.access pointers config.arithmetic config.scalar
    config.isRawPointer config.usizeLayout config.pointeeLayout config.operands.dereference config.floats
    () state CopyCompilerFacts.destPointerLayout RootCompilerFacts.usizeLayout CopyCompilerFacts.byteLayout
    RootOffsetQueries.overflowLayout id tag base offset count entry
    (pointee_query options remaining span) (by decide +kernel)
    CopyCompilerFacts.byte_layout_shape.2.1 (by decide +kernel) rhs
    (RootOffsetQueries.overflow_query options remaining span) (by decide +kernel)
    arithmetic pointerWidth resolution cached present positive fits bounds

#print axioms byte_offset
end DuplicatePrefix.ActualOffset
