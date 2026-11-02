import duplicate_prefix.S02SeparateDestinationSharedSite
import duplicate_prefix.S02SeparateDestinationSharedBounds

namespace DuplicatePrefix.S02SeparateDestinationSharedSiteBounds
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- Numeric source prerequisites hold for the source row in the actual installed call. -/
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
    (tracker : MachineHooks.BorrowState)
    (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (installed : CompilerFrameContext.ActualFrame)
    (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (actual : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] installed post))
    (tracked : post.borrowTracker = some tracker)
    (live : post.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,sourceEntry)) :
    (0 : UInt64) < len ∧ reference.base+reference.offset ≠ 0 ∧
    len.toNat < 9223372036854775808 ∧
    reference.offset.toNat + len.toNat ≤ sourceEntry.allocation.byteSize.bytes.toNat ∧
    sourceEntry.allocation.extra.locations.size = sourceEntry.allocation.byteSize ∧
    sourceEntry.allocation.extra.nodes.size + 2 < 65536 ∧
    sourceEntry.allocation.extra.nodes.size + 2 ≤ 4294967295 ∧
    tracker.global.nextPointerTag.value.toNat + 1 < 18446744073709551615 := by
  obtain ⟨other,otherTracker,otherFrame,otherPost,otherEntry,_child,_raw,otherActual,otherTracked,
      otherLive,sourceEq,counter,_tag,_parent,_offset,_len,_runtime,_activity⟩ :=
    S02SeparateDestinationSharedExact.after_exact id tag address len count input nonempty different
      returnTag returnConcrete
  have same : Storage.withCurrent #[] otherFrame otherPost = Storage.withCurrent #[] installed post :=
    (EStateM.Result.ok.inj (otherActual.symm.trans actual)).2
  have postEq : otherPost = post := congrArg (fun s : RootState => s.machine) same
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
    rw [postEq,idEq] at h
    exact congrArg Prod.snd (Option.some.inj (h.symm.trans live))
  have trackerEq : otherTracker = tracker :=
    Option.some.inj (by rw [postEq] at otherTracked; exact otherTracked.symm.trans tracked)
  obtain ⟨positive,nonzero,signed,bounds,capacity,nodes,nodeUInt,tagRoom⟩ :=
    S02SeparateDestinationSharedBounds.of_exact_source id tag address len input other otherEntry
      sourceEq otherTracker counter
  have localBounds : reference.offset.toNat + len.toNat ≤ sourceEntry.allocation.byteSize.bytes.toNat := by
    rw [←currentEq,sourceEq,entryEq]
    change reference.offset.toNat + len.toNat ≤ reference.entry.allocation.byteSize.bytes.toNat
    rw [reference.size]
    simpa only [Size.ofBytes] using reference.storage.bounds
  rw [currentEq] at capacity nodes nodeUInt
  rw [trackerEq] at tagRoom
  exact ⟨positive,by rw [←reference.pointerAddress]; exact reference.nonnull,
    signed,localBounds,capacity,nodes,nodeUInt,tagRoom⟩

end
end DuplicatePrefix.S02SeparateDestinationSharedSiteBounds

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationSharedSiteBounds.at_actual_call) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate site bounds dependency {dependency}"
