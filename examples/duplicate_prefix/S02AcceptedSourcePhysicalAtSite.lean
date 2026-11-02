import duplicate_prefix.S02SeparateDestinationSharedExact
import duplicate_prefix.S02AcceptedDefaultReadyGraph

namespace DuplicatePrefix.S02AcceptedSourcePhysicalAtSite
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Physical source facts at the actual installed call, for an arbitrary
concrete positive borrow and a distinct concrete return allocation. -/
theorem at_actual_call
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
    (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (installed : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (actual : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] installed machine))
    (live : machine.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,sourceEntry))
    (within : count ≤ len/2) :
    sourceEntry.allocation.len = sourceEntry.allocation.byteSize.bytes.toNat ∧
    InitMaskCopy.WellFormed sourceEntry.allocation.initializationMask ∧
    sourceEntry.allocation.initializationMask.len = sourceEntry.allocation.byteSize ∧
    InitMaskCopy.InitializedOn sourceEntry.allocation.initializationMask
      (Size.ofBytes reference.offset) (Size.ofBytes (reference.offset+count)) ∧
    ProvenanceCopy.WellFormed sourceEntry.allocation.provenanceMap sourceEntry.allocation.len ∧
    sourceEntry.allocation.len+64 < 18446744073709551616 ∧
    sourceEntry.allocation.mutability = .Mut := by
  obtain ⟨other,otherTracker,otherFrame,otherPost,otherEntry,_child,_raw,otherActual,
      _otherTracked,otherLive,sourceEq,_counter,_tag,_parent,_offset,_length,_runtime,_activity⟩ :=
    S02SeparateDestinationSharedExact.after_exact id tag address len count input nonempty different
      returnTag returnConcrete
  have same : Storage.withCurrent #[] otherFrame otherPost = Storage.withCurrent #[] installed machine :=
    (EStateM.Result.ok.inj (otherActual.symm.trans actual)).2
  have machineEq : otherPost = machine := congrArg (fun s : RootState => s.machine) same
  have idEq : other.id = reference.id := by
    have h1 := other.binding
    have h2 := reference.binding
    simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at h1 h2
    exact h1.1.symm.trans h2.1
  have entryEq : other.entry = reference.entry := by
    have h := other.live
    rw [idEq] at h
    exact congrArg Prod.snd (Option.some.inj (h.symm.trans reference.live))
  have currentEq : otherEntry = sourceEntry := by
    have h := otherLive
    rw [machineEq,idEq] at h
    exact congrArg Prod.snd (Option.some.inj (h.symm.trans live))
  have fields : sourceEntry.allocation.len = reference.entry.allocation.len ∧
      sourceEntry.allocation.byteSize = reference.entry.allocation.byteSize ∧
      sourceEntry.allocation.initializationMask = reference.entry.allocation.initializationMask ∧
      sourceEntry.allocation.provenanceMap = reference.entry.allocation.provenanceMap ∧
      sourceEntry.allocation.mutability = reference.entry.allocation.mutability := by
    rw [←currentEq,sourceEq,entryEq]
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  obtain ⟨storageEq,sizeEq,maskEq,provenanceEq,mutableEq⟩ := fields
  have storage : sourceEntry.allocation.len = sourceEntry.allocation.byteSize.bytes.toNat := by
    rw [storageEq,sizeEq,reference.size]
    exact reference.bytes
  have maskValid : InitMaskCopy.WellFormed sourceEntry.allocation.initializationMask := by
    rw [maskEq]; exact reference.storage.maskValid
  have maskLen : sourceEntry.allocation.initializationMask.len = sourceEntry.allocation.byteSize := by
    rw [maskEq,sizeEq,reference.size]
    exact reference.storage.maskLength
  have initialized : InitMaskCopy.InitializedOn sourceEntry.allocation.initializationMask
      (Size.ofBytes reference.offset) (Size.ofBytes (reference.offset+count)) := by
    rw [maskEq]
    exact DuplicatePrefixSliceStorage.accepted_initialized _ _ _ _ _ reference.storage within
  have provenance : ProvenanceCopy.WellFormed sourceEntry.allocation.provenanceMap sourceEntry.allocation.len := by
    rw [provenanceEq,storageEq]
    exact reference.provenanceMap
  have member : (reference.id,reference.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some reference.live)
  have fits : sourceEntry.allocation.len+64 < 18446744073709551616 := by
    rw [storageEq]
    simpa only using input.contract.resources.storageRoom (reference.id,reference.entry) member
  exact ⟨storage,maskValid,maskLen,initialized,provenance,fits,mutableEq.trans reference.mutable⟩

end
end DuplicatePrefix.S02AcceptedSourcePhysicalAtSite

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02AcceptedSourcePhysicalAtSite.at_actual_call) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved accepted physical source dependency {dependency}"
