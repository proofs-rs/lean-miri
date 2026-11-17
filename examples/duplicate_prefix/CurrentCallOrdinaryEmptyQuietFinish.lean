import duplicate_prefix.CurrentCallEmptyReturnCore
import duplicate_prefix.CurrentCallEmptyPointerDifferentFinish
import duplicate_prefix.CurrentCallEmptyEntrySourceData

namespace DuplicatePrefix.CurrentCallOrdinaryEmptyQuietFinish
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Common all-count continuation for a real dormant zero q row in a separate
allocation from Bool. The entry equation and every resource describe the SAME
actual post-Bool machine. No source byte ownership or new body is introduced. -/
theorem finish {options limits remaining span before argument place machine tracker}
    (count : UInt64) (R : CurrentCallPostEntryCheckpoint.Return machine tracker place)
    (sourceId : AllocId) (sourceTag : BorTag) (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (sourceLive : machine.memory.live.find? (fun row=>row.1==sourceId)=some (sourceId,sourceEntry))
    (different : sourceId≠R.id)
    (sourceRuntime : DuplicatePrefixBorrowContract.RuntimeFacts sourceEntry.allocation.extra tracker.global)
    (sourceRoom : sourceEntry.allocation.extra.nodes.size+2≤4294967295)
    (leaf : CurrentCallEmptyEntrySourceData.Leaf sourceEntry.allocation.extra sourceTag)
    (sourceHiddenOnBool : ∀index node,R.window.allocation.extra.nodes.get index=some node→node.tag=sourceTag→node.isExposed=false)
    (base sourceOffset : UInt64) (nonnull : base+sourceOffset≠0)
    (cached : machine.user.addresses.baseAddr.find? (fun row=>row.allocId==sourceId)=some ⟨sourceId,base⟩)
    (root : RootFrame) (raw : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (stop : root.frame.returnContinuation=.stop true)
    (destination : root.frame.returnPlace.toRuntimePlace=⟨.memory place.mplace,place.layout⟩) (varargs : root.frame.vaList=#[])
    (model : DuplicatePrefixCallModel.Model options remaining span machine)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins machine.user.payload.payload.user.types)
    (tracked : machine.borrowTracker=some tracker)
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread?=some thread)
    (top : thread.topUserRelevantFrame=some 0)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+1<18446744073709551615)
    (dynamicFuel validationFuel budget : Nat) (dynamicEq : options.place.dynamicFuel=dynamicFuel+1)
    (validationEq : options.limits.validation=validationFuel+1) (dispatchEq : limits.callDispatch=budget+1) :
    let updated:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete sourceId sourceTag) (Size.ofBytes (base+sourceOffset))) 0 ActualReferenceMetadata.reference).imm
    let sourceFrame:=({} : FrameState).addProtector sourceId sourceTag
    let frame:=CurrentCallEmptyProtocolControl.frame root updated sourceFrame count R.id R.node.tag
    Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base argument 0),.Copy (second count)]
      false (.memory place) (.stop true) (⟨⟨#[]⟩,before⟩ : RootState)=.ok () (Storage.withCurrent #[] frame machine)→
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument 0 count place := by
  intro updated sourceFrame frame entered
  obtain ⟨index,node,tagged,nodeAt,nodeTag,children,hidden,inactive⟩:=leaf
  have quiet:=CurrentCallResourceEmptyRootRelease.quiescent_of_inactive sourceEntry.allocation.extra index node inactive
  let ledger : CurrentCallEmptyLedgerRelease.SourceLedger machine R.window.allocation.extra (some (sourceId,sourceTag)):=
    .live sourceId sourceTag sourceEntry sourceLive index node tagged nodeAt hidden quiet sourceHiddenOnBool
  let core:=CurrentCallEmptyReturnCore.of_return R (some (sourceId,sourceTag)) ledger
    (sourceFrame.addProtector R.id R.node.tag) rfl model tracked thread active
  have borrowCore : core.borrowFrame=sourceFrame.addProtector R.id core.node.tag:=rfl
  obtain ⟨final,trace,terminal,empty⟩ : ∃final,SuccessfulTrace.Trace (config options (remaining+1) span) limits
      (Storage.withCurrent #[] frame machine) final ∧ExecutionMachine.step (config options (remaining+1) span) limits () final=(final,.ok false) ∧final.stack.frames=#[] := by
    by_cases zero : count=0
    · subst count
      exact CurrentCallEmptyContinuation.zero core limits root updated sourceFrame raw borrowCore stop destination varargs validationFuel validationEq
    · have done:=CurrentCallEmptyPointerDifferentFinish.finish options limits remaining span place R.original R.originalId R.window R.physical
        core.binding R.physicalId R.physicalOffset R.originalPointer.symm R.physicalAllocation R.originalIssued R.originalBinding R.runtime R.distinct R.short
        core.concrete R.node R.nodeAt R.hidden R.activity sourceId sourceEntry sourceLive different sourceRuntime sourceRoom sourceTag index node tagged nodeAt
        hidden quiet sourceHiddenOnBool base sourceOffset count nonnull zero cached root raw frame
        (CurrentCallEmptyProtocolControl.frame_some root updated {} sourceId sourceTag count R.id R.node.tag)
        stop destination varargs model origins tracked thread active top R.edge core.physicalReady tagRoom dynamicFuel validationFuel budget dynamicEq validationEq dispatchEq
      exact done
  let start:=Storage.withCurrent #[] frame machine
  let context : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit:=⟨config options (remaining+1) span,limits,fun _ _=>True⟩
  have callEntry : CallSafety.IsCallEntry 1 start:=⟨by decide,rfl⟩
  have past : CallSafety.pastCallBoundary 1 final:=by change final.stack.frames.size<1;rw [empty];decide
  exact ⟨start,final,entered,trace,terminal,empty,SuccessfulTrace.no_errors context 1 start final callEntry trace past,
    SuccessfulTrace.no_ub context 1 start final callEntry trace past,SuccessfulTraceTerminal.prefix_step_success trace terminal⟩
end
end DuplicatePrefix.CurrentCallOrdinaryEmptyQuietFinish
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallOrdinaryEmptyQuietFinish.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved ordinary empty quiet continuation dependency {name}: {dependency}"
