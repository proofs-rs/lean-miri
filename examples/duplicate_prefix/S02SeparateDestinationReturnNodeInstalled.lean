import duplicate_prefix.S02SeparateDestinationMetadataLiteral
import duplicate_prefix.S02SeparateDestinationReturnChild
import duplicate_prefix.S02SeparateDestinationReady
import duplicate_prefix.S02SeparateDestinationTransport
import duplicate_prefix.S02ConcreteCallPreamble
import duplicate_prefix.S02PositiveFinishFrame
import duplicate_prefix.RootEntryFinish

namespace DuplicatePrefix.S02SeparateDestinationReturnNodeInstalled
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
noncomputable section

/-- Actual installed call state retains the concrete return child packet
produced by the real post-argument protection and uninit write. -/
theorem enters_node
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (firstFresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615),
      let rawMachine := RawRootInvocation.machine #[] before
      let current := GeneralBorrowRawFnEntryScope.resultMachine rawMachine reference.tracker firstFresh
        reference.id reference.entry tag reference.offset len
      let root := RawRootInvocation.root before place input.contract.model.noDataRace
      let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
          (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
      ∃ (destination : DuplicatePrefixReturnPlaceInput.Input current place)
        (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
        (updated : Allocation Provenance BorrowTree) (child : UniIndex),
        let frame := (RootArgumentsTwo.result
          (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
            reference.id reference.tracker.global.nextPointerTag) count).frame
        let changed := {frame with location := .unwinding ⟨601⟩}
        let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
        let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra
          destination.tracker returnTag destination.offset 1
        let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
        let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id
          destination.tracker.global.nextPointerTag
        let installed := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
        let global := TypedBorrowSteps.registeredGlobal
          (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
          destination.tracker.global.nextPointerTag
        Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
          RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
          #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
            (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
            .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
          ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] installed after.machine) ∧
        updated.extra.indexOfTag destination.tracker.global.nextPointerTag = some child ∧
        DuplicatePrefixBorrowContract.RuntimeFacts updated.extra global ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive updated.extra global.protectedTags
          (some child) destination.selectedRoot destination.maximum destination.offset 1) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin updated.extra child .Write
          destination.offset (destination.offset+1) ∧
        ∃ parent node, updated.extra.indexOfTag returnTag = some parent ∧
          updated.extra.nodeAt child = some node ∧
          node.tag = destination.tracker.global.nextPointerTag ∧
          node.parent = some parent ∧ node.children = #[] ∧ node.isExposed = false := by
  obtain ⟨reference,firstFresh,argument,destination,secondFresh,updated,child,
      protect,extra,bytes,length,mutable,maskWf,maskLen,pointers,afterRuntime,afterOrder,lookup,
      positive,active⟩ := S02SeparateDestinationMetadataLiteral.concrete_after_argument_literal
    id tag address len count input nonempty different returnTag returnConcrete
  let machine := RawRootInvocation.machine #[] before
  let current := GeneralBorrowRawFnEntryScope.resultMachine machine reference.tracker firstFresh
    reference.id reference.entry tag reference.offset len
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
  let frame := (RootArgumentsTwo.result
    (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
      reference.id reference.tracker.global.nextPointerTag) count).frame
  let changed := {frame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra
    destination.tracker returnTag destination.offset 1
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id destination.tracker.global.nextPointerTag
  let installed := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
  let done := Storage.withCurrent #[] installed after.machine
  have shape := S02PositiveFinishFrame.after_destination_registration root
    (RawRootInvocation.locals before place input.contract.model.noDataRace)
    adjusted count reference.id destination.id reference.tracker.global.nextPointerTag
    destination.tracker.global.nextPointerTag
  obtain ⟨body,size,dead,noClocks⟩ := shape
  have finish := RootEntryFinish.actual_finish options limits (remaining+1) span #[] protectedFrame after.machine
    body size (dead ⟨0,by decide⟩ (by omega) (Or.inl rfl))
    (dead ⟨6,by decide⟩ (by omega) (Or.inr (Or.inl rfl)))
    (dead ⟨13,by decide⟩ (by omega) (Or.inr (Or.inr (Or.inl rfl))))
    (dead ⟨14,by decide⟩ (by omega) (Or.inr (Or.inr (Or.inr rfl)))) noClocks
  let h := ExecutionMachine.callHooks (config options (remaining+1) span) limits
  have localSpan := CallEntryLocals.root_span0 options limits (remaining+1) span #[] frame current
    (by rfl) (by rfl) (by rfl)
  have getFrame := CallEntryLocals.get_frame options limits (remaining+1) span #[] frame current
  have setFrame := CallEntryLocals.set_frame options limits (remaining+1) span #[] frame changed current
  have compat : h.checkArgumentCompat () RootCompilerFacts.rootAbi.ret RootCompilerFacts.rootAbi.ret
      (Storage.withCurrent #[] changed current) = .ok true (Storage.withCurrent #[] changed current) := by
    change (config options (remaining+1) span).calls.compiler.checkArgumentCompat () _ _ _ = _
    rw [(actual_fields options () (remaining+1) span).callCompiler]
    exact CallEntryFacts.root_return_argument_compat _ options.compatibilityBudget _
  have tail : RootEntryTail.tail h place (Storage.withCurrent #[] frame current) = .ok () done := by
    unfold RootEntryTail.tail RootCallCore.spanAt
    simp only [bind,EStateM.bind]
    rw [localSpan]
    simp only [EStateM.bind]
    rw [getFrame]
    simp only [EStateM.bind]
    dsimp only [changed] at setFrame
    rw [setFrame]
    simp only [EStateM.bind]
    dsimp only [changed] at compat
    rw [compat]
    simp only [EStateM.bind,Bool.not_true,ite_false,pure,EStateM.pure]
    change (do
      TypedRetag.protectInPlaceFunctionArgument
        (config options (remaining+1) span).retag limits.retag place
      RootEntryFinish.finish h) (Storage.withCurrent #[] changed current) = .ok () done
    simp only [bind,EStateM.bind]
    rw [protect]
    simp only [EStateM.bind]
    change RootEntryFinish.finish
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      (Storage.withCurrent #[] protectedFrame after.machine) = .ok () done
    exact finish
  obtain ⟨preambleAfter,preambleArg,preambleContinue⟩ :=
    S02ConcreteCallPreamble.prefix_and_continuation id tag address len count input nonempty
  have sameAfter : preambleAfter = Storage.withCurrent #[] frame current := by
    have resultEq := preambleArg.symm.trans argument
    exact (EStateM.Result.ok.inj resultEq).2
  have actualCall := preambleContinue done (sameAfter ▸ tail)
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts updated.extra
      (TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
        destination.tracker.global.nextPointerTag) := by rw [extra]; exact afterRuntime
  have positiveCurrent : Nonempty (DuplicatePrefixBorrowAuthorization.Positive updated.extra
      (TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
        destination.tracker.global.nextPointerTag).protectedTags
      (some child) destination.selectedRoot destination.maximum destination.offset 1) := by rw [extra]; exact positive
  have activeCurrent : GeneralBorrowFreshActiveWithin.ActiveWithin updated.extra child .Write
      destination.offset (destination.offset+1) := by rw [extra]; exact active
  have taggedCurrent : updated.extra.indexOfTag destination.tracker.global.nextPointerTag = some child := by
    rw [extra]; exact lookup
  have idEq : id = reference.id := by
    have binding := reference.binding
    simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at binding
    exact binding.1
  have destId : destination.id = input.contract.destination.id := by
    have physical := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
    have provenance := congrArg (fun ptr : Pointer (Option Provenance) => ptr.provenance) physical
    simp only [Pointer.withOptionalProvenance] at provenance
    have same := Option.some.inj provenance
    have concrete : destination.pointer.provenance = .concrete input.contract.destination.id returnTag :=
      same.trans returnConcrete
    have binding := destination.binding
    simp only [DuplicatePrefixReferenceInput.Binding,concrete] at binding
    exact binding.1.symm
  have destEntry : destination.entry = input.contract.destination.entry := by
    have other : reference.id ≠ destination.id := by simpa only [←destId,←idEq] using different
    have live : current.memory.live.find? (fun row => row.1 == destination.id) =
        some (destination.id,input.contract.destination.entry) := by
      change (RetagEntry.updatedMemory (RawRootInvocation.machine #[] before).memory reference.id
        reference.entry (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
          reference.tracker tag reference.offset len)).live.find? (fun row => row.1 == destination.id) = _
      rw [S02SeparateDestinationTransport.other_live _ _ _ _ _ other]
      have preserved := (RawRootInvocation.preservation #[] before).1
      rw [preserved,destId]
      exact input.contract.destination.live
    exact congrArg Prod.snd (Option.some.inj (destination.live.symm.trans live))
  obtain ⟨currentRuntime,roots,order,headroom,_fresh⟩ :=
    S02SeparateDestinationReady.local_facts_after_argument input reference firstFresh destination destEntry
  have concrete : destination.pointer.provenance = .concrete destination.id returnTag := by
    have physical := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
    have provenance := congrArg (fun ptr : Pointer (Option Provenance) => ptr.provenance) physical
    simp only [Pointer.withOptionalProvenance] at provenance
    rw [Option.some.inj provenance,destId]
    exact returnConcrete
  obtain ⟨parent,childNode,node,parentTagged,childTagged,present,same,edge,leaf,hidden⟩ :=
    S02SeparateDestinationReturnChild.run destination currentRuntime roots order headroom secondFresh
      returnTag concrete
  have childEq : childNode = child := Option.some.inj (childTagged.symm.trans (by rw [←extra]; exact taggedCurrent))
  subst childNode
  rw [←extra] at parentTagged present
  exact ⟨reference,firstFresh,destination,secondFresh,updated,child,actualCall,taggedCurrent,runtime,
    positiveCurrent,activeCurrent,parent,node,parentTagged,present,same,edge,leaf,hidden⟩

end
end DuplicatePrefix.S02SeparateDestinationReturnNodeInstalled

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationReturnNodeInstalled.enters_node) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination return installed dependency {dependency}"
