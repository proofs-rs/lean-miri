import duplicate_prefix.S02AcceptedDefaultReadySource
import duplicate_prefix.S02SeparateDestinationZeroCoreTagged
import duplicate_prefix.S02SeparateDestinationRejectedSourceNode
import duplicate_prefix.S02SeparateDestinationStateJoin

namespace DuplicatePrefix.S02AcceptedSourceNodeAtGuard
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The actual accepted call retains its original protected source node and
the exact installed borrow packet after the shared Ref/len guard. -/
theorem at_guard
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
    (countPositive : 0 < count.toNat) (within : count ≤ len/2) :
    ∃ (entry result : CompilerFrameContext.ActualFrame)
      (initial post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
      (tracker held : MachineHooks.BorrowState)
      (sourceRaw : GeneralBorrowRawShared.Input sourceEntry.allocation.extra tracker.global)
      (finalTree : BorrowTree)
      (packet : S02SeparateDestinationZeroCore.Packet entry initial place)
      (node : TreeNode),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] entry initial) ∧
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] entry initial) (Storage.withCurrent #[] result post) ∧
      result.location = .mir ⟨6,7⟩ ∧
      initial.borrowTracker = some tracker ∧
      GeneralBorrowRawSharedToLenLedger.Graph sourceEntry.allocation.extra finalTree sourceRaw.selected tracker held ∧
      packet.sourceId = reference.id ∧ packet.sourceTag = sourceRaw.parentTag ∧
      packet.sourceEntry = sourceEntry ∧ packet.sourceChild = sourceRaw.parent ∧
      finalTree.nodeAt sourceRaw.parent = some node ∧ node.tag = sourceRaw.parentTag ∧
      node.isExposed = false ∧ finalTree.indexOfTag sourceRaw.parentTag = some sourceRaw.parent := by
  obtain ⟨entry,result,initial,post,reference,sourceEntry,tracker,sourceRaw,finalTree,held,raw,
    actual,trace,located,_size,_body,_identity,_callee,_slot13,_slot15,_slot16,_immediate,_extraEq,_trackEq,
    _noClocks,_slot0,_sourceCell,_countCell,_high,live,_memory,_oldActivity,_storage,_maskValid,_maskLen,
    _initialized,_provenance,_storageFits,_mutable,_sourceExtras,initialTracked,_postTracked,_modeEq,
    _ghost,_shallow,_race,_addresses,_types,_extras,_backend,_unchecked,_noGc,_fixed,_thread,
    _runtime,graph,_positive,_nonzero,_signed,_bounds,_sourceCapacity,_nodeMargin,_tagMargin,
    sourceRawTag,rawTag,_rawOffset,_rawLen⟩ :=
    S02AcceptedDefaultReadySource.after_guard_source id tag address len count input nonempty different
      returnTag returnConcrete countPositive within
  obtain ⟨otherFrame,otherMachine,otherActual,packet,sourceSame⟩ :=
    S02SeparateDestinationZeroCoreTagged.enters id tag address len count input nonempty different
      returnTag returnConcrete
  have same : Storage.withCurrent #[] otherFrame otherMachine = Storage.withCurrent #[] entry initial :=
    (EStateM.Result.ok.inj (otherActual.symm.trans actual)).2
  have frameEq : otherFrame = entry :=
    S02SeparateDestinationStateJoin.same_frame otherFrame entry otherMachine initial same
  have machineEq : otherMachine = initial :=
    S02SeparateDestinationPacketJoin.same_machine otherFrame entry otherMachine initial same
  subst otherFrame
  subst otherMachine
  obtain ⟨sourceId,sourceTag,sourceEntryEq,sourceChild,node,present,nodeTag,hidden,tagged⟩ :=
    S02SeparateDestinationRejectedSourceNode.preserved id tag address len count input nonempty
      different returnTag returnConcrete reference tracker held sourceEntry sourceRaw entry initial
      actual packet sourceSame live sourceRawTag finalTree graph
  exact ⟨entry,result,initial,post,reference,sourceEntry,tracker,held,sourceRaw,finalTree,packet,node,
    actual,trace,located,initialTracked,graph,sourceId,sourceTag,sourceEntryEq,sourceChild,
    present,nodeTag,hidden,tagged⟩

end
end DuplicatePrefix.S02AcceptedSourceNodeAtGuard

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02AcceptedSourceNodeAtGuard.at_guard) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved accepted source node guard dependency {dependency}"
