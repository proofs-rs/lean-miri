import duplicate_prefix.CopyHelperSteps
import duplicate_prefix.CopyHelperIntrinsic
namespace DuplicatePrefix.CopyHelperMemory
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem actual_initialized_copy_step
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (location : frame.location = .mir ⟨7,8⟩)
    (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : BorTag)
    (tags : Fin 6 → BorTag) (base offset sliceLen n : UInt64) (kind : MemoryKind MiriMemoryKind)
    (allocation : Allocation Provenance BorrowTree)
    (positive : 0 < n)
    (sliceBounds : offset.toNat + sliceLen.toNat ≤ allocation.byteSize.bytes.toNat)
    (copyBounds : n.toNat + n.toNat ≤ sliceLen.toNat)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (maskValid : InitMaskCopy.WellFormed allocation.initializationMask)
    (maskLen : allocation.initializationMask.len = allocation.byteSize)
    (initialized : InitMaskCopy.InitializedOn allocation.initializationMask
      (Size.ofBytes offset) (Size.ofBytes (offset + n)))
    (valid : ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len)
    (storageFits : allocation.len + 64 < 18446744073709551616)
    (mutable : allocation.mutability = .Mut)
    (noClocks : machine.dataRace = none)
    (noBackend : machine.user.payload.payload.user.backend = .none)
    (tracked : machine.borrowTracker = some tracker)
    (extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) =
      some (id, ⟨none, #[]⟩))
    (live : machine.memory.live.find? (fun row => row.1 == id) = some (id, ⟨kind, allocation⟩))
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩)
    (distinct : Function.Injective tags)
    (tagAt : tag = tags 5)
    (tree : allocation.extra = NestedBorrowAccess.nestedTree tags
      (BorrowRangeAccess.partitionWithInside allocation.byteSize.bytes offset (offset + sliceLen)
        BorrowRangeAccess.rootLocation (NestedBorrowAccess.nestedLocation false)))
    (protectionMask : ProtectedBorrowAccess.SixMask tags tracker.global.protectedTags false)
    (bounded : n ≤ (PreparedContracts.actualConfig options () remaining span).projection.maxSizeOfVal.bytes)
    (valid14 : (14 : MIR.LocalId) < frame.locals.size)
    (valid15 : (15 : MIR.LocalId) < frame.locals.size)
    (valid16 : (16 : MIR.LocalId) < frame.locals.size)
    (live14 : frame.locals[14].value = .live (.immediate (.scalar (Scalar.fromPointer
      (PreparedContracts.actualConfig options () remaining span).access.runtime.base
      (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset)))))))
    (live15 : frame.locals[15].value = .live (.immediate (.scalar (Scalar.fromPointer
      (PreparedContracts.actualConfig options () remaining span).access.runtime.base
      (Pointer.new (.concrete id tag) (Size.ofBytes (base+(offset+n))))))))
    (live16 : frame.locals[16].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (cache14 : frame.locals[14].layout = some CopyCompilerFacts.sourcePointerLayout)
    (cache15 : frame.locals[15].layout = some CopyCompilerFacts.destPointerLayout)
    (cache16 : frame.locals[16].layout = some RootCompilerFacts.usizeLayout)
    (localClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) :
    let config := PreparedContracts.actualConfig options () remaining span
    let state := Storage.withCurrent frames frame machine
    let readAccess := allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
    let readState := CanonicalCopy.replaceAllocation state id kind (allocation.setExtra readAccess.tree)
    let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes (offset+n)) (Size.ofBytes n) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
    let writeState := CanonicalCopy.replaceAllocation readState id kind ((allocation.setExtra readAccess.tree).setExtra writeAccess.tree)
    ∃ result,
      ExecutionMachine.step config limits () state =
        (Storage.withCurrent frames {frame with location := .mir ⟨7,9⟩}
          (CanonicalCopy.replaceAllocation writeState id kind result).machine,.ok true) ∧
      result.byteSize = allocation.byteSize ∧ result.len = allocation.len ∧
      result.extra = writeAccess.tree ∧
      AllocationCopy.snapshot result = (AllocationCopy.snapshot allocation).extract 0 (offset+n).toNat ++
        (AllocationCopy.snapshot allocation).extract offset.toNat (offset+n).toNat ++
        (AllocationCopy.snapshot allocation).extract (offset+n+n).toNat allocation.len := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent frames frame machine
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨context, accessEq, arithmeticEq, alignment⟩ := fields.canonicalCopy
  have width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩ :=
    arithmeticEq.symm.trans (CanonicalConfigFacts.actual_arithmetic options () remaining span)
  have copy := CanonicalCopy.canonical_nested_initialized_copy context state tracker id tag tags base offset sliceLen n kind allocation
    width positive sliceBounds copyBounds storage maskValid maskLen initialized valid storageFits mutable noClocks noBackend
    tracked extras live cached distinct tagAt tree protectionMask
  dsimp only at copy
  obtain ⟨result, copied, sizeEq, lenEq, treeEq, bytesEq⟩ := copy
  refine ⟨result, ?_,sizeEq,lenEq,treeEq,bytesEq⟩
  obtain ⟨other,otherArithmetic,otherResolve,reduction⟩ := CopyHelperIntrinsic.actual_generic_copy options limits remaining span debugOff
    frames frame machine (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset)))
    (Pointer.new (.concrete id tag) (Size.ofBytes (base+(offset+n)))) n valid14 valid15 valid16
    live14 live15 live16 cache14 cache15 cache16 localClocks ghost bounded
  rw [← otherArithmetic,arithmeticEq,accessEq] at reduction
  let readAccess := allocation.extra.performBorrowAccessRange (.concrete tag)
    (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
  let readState := CanonicalCopy.replaceAllocation state id kind (allocation.setExtra readAccess.tree)
  let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete tag)
    (Size.ofBytes (offset+n)) (Size.ofBytes n) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
  let writeState := CanonicalCopy.replaceAllocation readState id kind ((allocation.setExtra readAccess.tree).setExtra writeAccess.tree)
  let finalMachine := (CanonicalCopy.replaceAllocation writeState id kind result).machine
  have effect : (ExecutionMachine.stepHooks config limits).intrinsic ()
      (.CopyNonOverlapping ⟨.Move ⟨14,#[]⟩,.Move ⟨15,#[]⟩,.Move ⟨16,#[]⟩⟩) state =
      (Storage.withCurrent frames frame finalMachine,.ok ()) := by
    rw [reduction]
    unfold MachineHooks.run Call.run
    simp only [Pointer.withOptionalProvenance, Pointer.new, state] at copied ⊢
    rw [copied]
    rfl
  exact CopyHelperSteps.intrinsic_of_actual_effect config limits frames frame frame machine finalMachine
    ⟨7,8⟩ _ location location (by rw [sourceBody];exact CopyHelperFacts.copy_intrinsic_statement) effect

#print axioms actual_initialized_copy_step
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``actual_initialized_copy_step) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved axiom {dependency}"
end DuplicatePrefix.CopyHelperMemory
