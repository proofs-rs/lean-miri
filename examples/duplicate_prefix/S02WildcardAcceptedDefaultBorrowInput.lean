import duplicate_prefix.S02WildcardAcceptedSharedLedgerShape
import duplicate_prefix.S02PostLenMutableInput
import duplicate_prefix.GeneralBorrowRawDefault

namespace DuplicatePrefix.S02WildcardAcceptedDefaultBorrowInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The actual accepted shared Ref/len leaves a usable Default mutable-borrow
input at MIR6,7, with two constructor slots still available. -/
theorem ready
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (countPositive : 0 < count.toNat) (within : count ≤ len/2)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new .wildcard (Size.ofBytes address)) len),
      reference.id ≠ input.contract.destination.id →
    ∃ (entry result : CompilerFrameContext.ActualFrame)
      (machine post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
      (finalTree : BorrowTree) (held : MachineHooks.BorrowState)
      (defaultRaw : GeneralBorrowRawDefault.Input finalTree held.global),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] entry machine) ∧
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] entry machine) (Storage.withCurrent #[] result post) ∧
      result.location = .mir ⟨6,7⟩ ∧
      post.memory = RetagEntry.updatedMemory machine.memory reference.id sourceEntry finalTree ∧
      post.borrowTracker = some held ∧
      DuplicatePrefixBorrowContract.RuntimeFacts finalTree held.global ∧
      defaultRaw.parentTag = reference.tracker.global.nextPointerTag ∧
      defaultRaw.offset = reference.offset ∧ defaultRaw.len = len ∧
      finalTree.nodes.size+2 < 65536 ∧
      held.global.nextPointerTag.value.toNat+1 < 18446744073709551615 := by
  obtain ⟨reference,ready⟩ := S02WildcardAcceptedSharedLedgerShape.executes
    address len count input nonempty countPositive within returnTag returnConcrete
  refine ⟨reference,?_⟩
  intro different
  obtain ⟨entry,frame,result,machine,post,packet,raw,finalTree,held,child,
    actual,prefixTrace,bodyTrace,location,size,body,identity,callee,extra,placeEq,
    continuation,varargs,localId,track,slot0,slot1,slot2,slot13,slot15,slot16,
    high,all,postMemory,postTracker,mode,runtime,⟨readPositive⟩,⟨bothPositive⟩,
    activity,graph,ghost,shallow,race,addresses,types,extras,backend,unchecked,noGc,
    fixed,⟨thread,active,topZero⟩,sourceId,sourceTag,rawParent,rawSelected,
    sourceSelected,rawMaximum,sourceOffset,sourceLen,sourceSame,frameLiteral,
    nodeMargin,tagMargin,shape,capacity,rawTag,rawOffset,rawLen,rawUser,defaultMode⟩ := ready different
  have parentPresent : packet.sourceEntry.allocation.extra.nodeAt raw.parent = some packet.sourceNode := by
    rw [rawParent]; exact packet.sourcePresent
  have parentTag : packet.sourceNode.tag = raw.parentTag := sourceSame.trans sourceTag
  have bothRaw : DuplicatePrefixBorrowAuthorization.Positive finalTree held.global.protectedTags
      (some raw.parent) (some raw.selected) raw.maximum raw.offset raw.len := by
    simpa only [rawOffset,rawLen] using bothPositive
  have currentTagRoom : held.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change held.global.nextPointerTag.value.toNat < 18446744073709551615
    have growth := graph.tagCounter
    omega
  obtain ⟨mutableRaw,tagEq,_parent,_selected,_maximum,offsetEq,lenEq⟩ :=
    S02PostLenMutableInput.from_graph packet.sourceEntry.allocation.extra finalTree packet.tracker held raw
      runtime packet.sourceNode parentPresent parentTag bothRaw graph currentTagRoom
  let defaultRaw : GeneralBorrowRawDefault.Input finalTree held.global := {
    parentTag := mutableRaw.parentTag, parent := mutableRaw.parent,
    selected := mutableRaw.selected, maximum := mutableRaw.maximum,
    offset := mutableRaw.offset, len := mutableRaw.len,
    tagged := mutableRaw.tagged, positive := mutableRaw.positive,
    distinct := mutableRaw.distinct, order := mutableRaw.order,
    short := mutableRaw.short, nodeRoom := mutableRaw.nodeRoom,
    tagRoom := mutableRaw.tagRoom }
  have tickMemory := (S02SeparateDestinationTickLedger.preserved options remaining span machine).1
  have postMemoryInitial : post.memory = RetagEntry.updatedMemory machine.memory reference.id packet.sourceEntry finalTree := by
    rw [tickMemory] at postMemory
    exact postMemory
  have afterMargin : finalTree.nodes.size+2 < 65536 ∧
      held.global.nextPointerTag.value.toNat+1 < 18446744073709551615 := by
    have nodeGrowth := graph.growth
    have tagGrowth := graph.tagCounter
    omega
  exact ⟨entry,result,machine,post,packet.sourceEntry,finalTree,held,defaultRaw,actual,
    SuccessfulTrace.append prefixTrace bodyTrace,location,postMemoryInitial,postTracker,runtime,
    tagEq.trans rawTag,offsetEq.trans rawOffset,lenEq.trans rawLen,afterMargin.1,afterMargin.2⟩

end
end DuplicatePrefix.S02WildcardAcceptedDefaultBorrowInput

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardAcceptedDefaultBorrowInput.ready) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard accepted default-input dependency {dependency}"
