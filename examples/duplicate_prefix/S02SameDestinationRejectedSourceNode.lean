import duplicate_prefix.S02SameDestinationPacketSourceIdentity
import duplicate_prefix.GeneralBorrowRawSharedToLenLedger

namespace DuplicatePrefix.S02SameDestinationRejectedSourceNode
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- The actual source protector's old node survives the shared Ref/len and rejected guard. -/
theorem preserved
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (sameAllocation : id = input.contract.destination.id)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
    (tracker held : MachineHooks.BorrowState)
    (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (raw : GeneralBorrowRawShared.Input sourceEntry.allocation.extra tracker.global)
    (entry : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (actual : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] entry machine))
    (packet : S02SameDestinationZeroCore.Packet entry machine place)
    (sourceSame : packet.sourceNode.tag = packet.sourceTag)
    (live : machine.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,sourceEntry))
    (rawTag : raw.parentTag = reference.tracker.global.nextPointerTag)
    (finalTree : BorrowTree)
    (graph : GeneralBorrowRawSharedToLenLedger.Graph sourceEntry.allocation.extra finalTree raw.selected tracker held) :
    packet.destination.id = reference.id ∧ packet.sourceTag = raw.parentTag ∧
    packet.destination.entry = sourceEntry ∧ packet.sourceChild = raw.parent ∧
    ∃ node, finalTree.nodeAt raw.parent = some node ∧ node.tag = raw.parentTag ∧
      node.isExposed = false ∧ finalTree.indexOfTag raw.parentTag = some raw.parent := by
  obtain ⟨sourceId,sourceTag⟩ :=
    S02SameDestinationPacketSourceIdentity.source_same id tag address len count input nonempty
      sameAllocation returnTag returnConcrete reference entry machine actual packet
  have tagEq : packet.sourceTag = raw.parentTag := sourceTag.trans rawTag.symm
  have packetLive := packet.destination.live
  rw [sourceId] at packetLive
  have sourceEq : packet.destination.entry = sourceEntry :=
    congrArg Prod.snd (Option.some.inj (packetLive.symm.trans live))
  have packetTag := packet.sourceTagged
  rw [sourceEq,tagEq] at packetTag
  have childEq : packet.sourceChild = raw.parent := Option.some.inj (packetTag.symm.trans raw.tagged)
  have oldPresent := packet.sourcePresent
  rw [sourceEq,childEq] at oldPresent
  obtain ⟨node,present,same,parent,hidden,lookup⟩ :=
    graph.oldNodes raw.parent packet.sourceNode oldPresent
  rw [sourceSame,tagEq] at lookup
  refine ⟨sourceId,tagEq,sourceEq,childEq,node,present,?_ ,?_,lookup⟩
  · exact same.trans (sourceSame.trans tagEq)
  · rw [hidden]
    exact packet.sourceHidden

end
end DuplicatePrefix.S02SameDestinationRejectedSourceNode

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SameDestinationRejectedSourceNode.preserved) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved rejected source node dependency {dependency}"
