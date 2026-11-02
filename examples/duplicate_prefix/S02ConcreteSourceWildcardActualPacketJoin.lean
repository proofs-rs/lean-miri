import duplicate_prefix.S02ConcreteSourceWildcardInstalledBothIdentity
import duplicate_prefix.S02ConcreteSourceWildcardActualTrueReturnSource
import duplicate_prefix.S02SeparateDestinationStateJoin

namespace DuplicatePrefix.S02ConcreteSourceWildcardActualPacketJoin
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Determinism of the actual stack-frame call joins the wildcard return
packet and hidden protected source node to the source-only copy proof. -/
theorem at_same_call
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
    (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (tracker held : MachineHooks.BorrowState)
    (sourceRaw : GeneralBorrowRawShared.Input sourceEntry.allocation.extra tracker.global)
    (entry : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (actual : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] entry machine))
    (sourceLive : machine.memory.live.find? (fun row => row.1 == reference.id) =
      some (reference.id,sourceEntry))
    (rawTag : sourceRaw.parentTag = reference.tracker.global.nextPointerTag)
    (finalTree : BorrowTree)
    (graph : GeneralBorrowRawSharedToLenLedger.Graph sourceEntry.allocation.extra finalTree
      sourceRaw.selected tracker held) :
    ∃ borrowFrame : FrameState,
      Nonempty (S02ConcreteSourceWildcardReturnPacket.ReturnPacket machine place
        reference.id sourceRaw.parentTag borrowFrame) ∧
      ∃ node : TreeNode,
        finalTree.nodeAt sourceRaw.parent = some node ∧
        finalTree.indexOfTag sourceRaw.parentTag = some sourceRaw.parent ∧
        node.tag = sourceRaw.parentTag ∧ node.isExposed = false := by
  obtain ⟨other,firstFresh,destination,secondFresh,tree,updated,otherActual,destId,
    ⟨returnPacket,packetId⟩,⟨sourcePacket⟩⟩ :=
    S02ConcreteSourceWildcardInstalledBothIdentity.enters_both_identity
      id tag address len count input nonempty different returnWildcard
  let current := GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
    other.tracker firstFresh other.id other.entry tag other.offset len
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete other.id other.tracker.global.nextPointerTag)
      (Size.ofBytes (other.base+other.offset))) len ActualReferenceMetadata.reference).imm
  let frame := (RootArgumentsTwo.result
    (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
      other.id other.tracker.global.nextPointerTag) count).frame
  let changed := {frame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector other.id other.tracker.global.nextPointerTag
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let borrowFrame := owned.addProtector destination.id destination.tracker.global.nextPointerTag
  let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id
    destination.tracker.global.nextPointerTag
  let installed := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
  have same : Storage.withCurrent #[] installed after.machine = Storage.withCurrent #[] entry machine :=
    (EStateM.Result.ok.inj (otherActual.symm.trans actual)).2
  have machineEq : after.machine = machine :=
    S02SeparateDestinationPacketJoin.same_machine installed entry after.machine machine same
  have idEq : other.id = reference.id := by
    have left := other.binding
    have right := reference.binding
    simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at left right
    exact left.1.symm.trans right.1
  have trackerEq : other.tracker = reference.tracker :=
    Option.some.inj (other.enabled.symm.trans reference.enabled)
  have tagEq : other.tracker.global.nextPointerTag = sourceRaw.parentTag := by
    rw [trackerEq,rawTag]
  have alignedPacket : S02ConcreteSourceWildcardReturnPacket.ReturnPacket machine place
      reference.id sourceRaw.parentTag borrowFrame := by
    have alignedMachine : S02ConcreteSourceWildcardReturnPacket.ReturnPacket machine place
        other.id other.tracker.global.nextPointerTag borrowFrame := by
      rw [←machineEq]
      exact returnPacket
    simpa only [idEq,tagEq] using alignedMachine
  have sourcePacketLive : machine.memory.live.find? (fun row => row.1 == reference.id) =
      some (reference.id,{other.entry with allocation := (other.entry.allocation.setExtra
        (GeneralBorrowRawFnEntryArgument.finalTree other.entry.allocation.extra
          other.tracker tag other.offset len))}) := by
    have alignedLive : machine.memory.live.find? (fun row => row.1 == other.id) =
        some (other.id,{other.entry with allocation := (other.entry.allocation.setExtra
          (GeneralBorrowRawFnEntryArgument.finalTree other.entry.allocation.extra
            other.tracker tag other.offset len))}) := by
      rw [←machineEq]
      exact sourcePacket.live
    simpa only [idEq] using alignedLive
  have sourceEntryEq : sourceEntry = {other.entry with allocation := (other.entry.allocation.setExtra
      (GeneralBorrowRawFnEntryArgument.finalTree other.entry.allocation.extra
        other.tracker tag other.offset len))} :=
    congrArg Prod.snd (Option.some.inj (sourceLive.symm.trans sourcePacketLive))
  have sourceTreeEq : sourceEntry.allocation.extra =
      GeneralBorrowRawFnEntryArgument.finalTree other.entry.allocation.extra
        other.tracker tag other.offset len := by
    rw [sourceEntryEq]
    rfl
  have childEq : sourcePacket.child = sourceRaw.parent := by
    have tagged := sourcePacket.tagged
    rw [←sourceTreeEq,tagEq] at tagged
    exact Option.some.inj (tagged.symm.trans sourceRaw.tagged)
  have sourcePresent : sourceEntry.allocation.extra.nodeAt sourceRaw.parent = some sourcePacket.node := by
    have present := sourcePacket.present
    rw [←sourceTreeEq,childEq] at present
    exact present
  obtain ⟨node,present,nodeTag,_parent,exposure,tagged⟩ :=
    graph.oldNodes sourceRaw.parent sourcePacket.node sourcePresent
  have sourceTag : sourcePacket.node.tag = sourceRaw.parentTag := sourcePacket.same.trans tagEq
  refine ⟨borrowFrame,⟨alignedPacket⟩,node,present,?_,?_,?_⟩
  · rw [←sourceTag]
    exact tagged
  · exact nodeTag.trans sourceTag
  · exact exposure.trans sourcePacket.hidden

end
end DuplicatePrefix.S02ConcreteSourceWildcardActualPacketJoin

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceWildcardActualPacketJoin.at_same_call) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source wildcard packet join dependency {dependency}"
