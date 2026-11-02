import duplicate_prefix.CurrentCallReferenceEntry
import duplicate_prefix.RootArgumentsTwo

/-! Actual positive two-argument entry from the original current-call proposal.
The new root frame and its local storage facts are derived from the real frame
constructor. One mode scope encloses both argument copies. Bool destination
protection and the function body remain subsequent stages. -/
namespace DuplicatePrefix.CurrentCallArguments
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallReferenceEntry
open CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def destination (place : MPlaceTy Provenance) : RuntimeStackPlace Provenance :=
  (⟨.memory place.mplace,place.layout⟩ : RuntimePlace Provenance).stackView

/-- Source initFrame creates this raw root and leaves the original machine
unchanged. The structural/local facts used below are consequences of that
constructor and subsequent actual storageLive, not caller certificates. -/
theorem creation (crates : Array Nat) (before : Before) (frames : Array CompilerFrameContext.ActualFrame)
    (place : MPlaceTy Provenance) (identity : LocalsIdentity) (race : before.dataRace = none) :
    MachineHooks.initFrame (FrameMetadata.userRelevance
      (CompilerFrameMetadata.hooks PreparedReflection.actual.compiler.lifecycle.frames crates))
      (Frame.create RootBody.reflected.body RootBody.reflected.functionInstance () (.stop true)
        (destination place) ⟨559⟩ identity) (⟨⟨frames⟩,before⟩ : RootState) =
      .ok (RootFrameData.raw before (destination place) identity race).frame (⟨⟨frames⟩,before⟩ : RootState) :=
  CallEntryFacts.init_root_frame crates (⟨⟨frames⟩,before⟩ : RootState) (destination place) identity

/-- The initial root is the actual constructor's data, not a caller's prepared
callee-frame certificate. Source/Bool allocation identities remain unrestricted. -/
theorem arguments (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (before : Before) (tracker : MachineHooks.BorrowState) (argument : DuplicatePrefixSliceArgument.Argument)
    (len : UInt64) (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frames : Array CompilerFrameContext.ActualFrame) (identity : LocalsIdentity)
    (positive : 0 < len.toNat) (count : UInt64) :
    let root := RootFrameData.raw before (destination place) identity input.machine.settings.noDataRace
    let prepared := firstLive root
    ∃ source : ViewedOutcome options remaining span ctx before tracker frames
        (copiedFrame options remaining span prepared.frame 1 (prepared.valid i1) argument len) {} argument len place call data .FnEntry true,
      ∃ validCopied : 1 < (copiedFrame options remaining span prepared.frame 1 (prepared.valid i1) argument len).locals.size,
      ∃ firstDone : RootFrame,
        firstDone.frame = writtenFrame source 1 validCopied ∧
        (RootArgumentsTwo.result firstDone count).frame.returnPlace = destination place ∧
        (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
          (RootCallCore.argumentBody (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
            (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base argument len) (second count))
          (Storage.withCurrent frames root.frame before) =
          .ok (2,2) (Storage.withCurrent frames (RootArgumentsTwo.result firstDone count).frame
            {validatedMachine source with borrowTracker := some ⟨source.base.raw.output.global,tracker.retagMode⟩}) := by
  let root := RootFrameData.raw before (destination place) identity input.machine.settings.noDataRace
  let prepared := firstLive root
  have rawLocals : root.frame.locals = Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout) :=
    RootEntryFrame.raw_locals before (destination place) identity
  have entry1 : (root.frame.locals[1]'(root.valid i1)) = (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
    have found : root.frame.locals[1]? = some (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by rw [rawLocals];rfl
    exact Option.some.inj ((Array.getElem?_eq_getElem (root.valid i1)).symm.trans found)
  have entry2 : (root.frame.locals[2]'(root.valid i2)) = (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
    have found : root.frame.locals[2]? = some (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by rw [rawLocals];rfl
    exact Option.some.inj ((Array.getElem?_eq_getElem (root.valid i2)).symm.trans found)
  have dead1 : (root.frame.locals[1]'(root.valid i1)).value = .dead := congrArg LocalState.value entry1
  have cache1 : (root.frame.locals[1]'(root.valid i1)).layout = none := congrArg LocalState.layout entry1
  have dead2 : (root.frame.locals[2]'(root.valid i2)).value = .dead := congrArg LocalState.value entry2
  have cache2 : (root.frame.locals[2]'(root.valid i2)).layout = none := congrArg LocalState.layout entry2
  have borrow : prepared.frame.extra.borrowTracker = some {} := by
    exact RootEntryFrame.raw_borrow before (destination place) identity tracker input.machine.state.enabled
  have live : (prepared.frame.locals[1]'(prepared.valid i1)).value = .live (.immediate .uninit) := by
    simp only [prepared,firstLive,RootFrameData.live,RootFrameData.write,Array.getElem_set_self,i1]
  have cached : (prepared.frame.locals[1]'(prepared.valid i1)).layout = some ActualReferenceMetadata.reference := by
    simp only [prepared,firstLive,RootFrameData.live,RootFrameData.write,firstCache,RootFrameData.cache,
      LocalOperands.cachedLayoutFrame,Array.getElem_set_self,i1]
  obtain ⟨source,validCopied,copy1⟩ := CurrentCallReferenceEntry.copy_argument options limits remaining span ctx before tracker argument len place call data input
    frames prepared.frame {} borrow positive 1 (prepared.valid i1) .uninit live cached prepared.noClocks
  let firstDone : RootFrame := {
    frame := writtenFrame source 1 validCopied
    size := by
      simpa only [writtenFrame,copiedFrame,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,Array.size_set] using prepared.size
    body := prepared.body
    identity := prepared.identity
    callee := prepared.callee
    noClocks := prepared.noClocks
  }
  have nextDead : (firstDone.frame.locals[2]'(firstDone.valid i2)).value = .dead := by
    simpa [firstDone,writtenFrame,copiedFrame,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,
      prepared,firstLive,RootFrameData.live,RootFrameData.write,firstCache,RootFrameData.cache,RootFrameData.atSpan,
      LocalOperands.cachedLayoutFrame,Array.getElem_set,i1,i2,show (2 : Nat) ≠ 1 by decide] using dead2
  have nextCache : (firstDone.frame.locals[2]'(firstDone.valid i2)).layout = none := by
    simpa [firstDone,writtenFrame,copiedFrame,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,
      prepared,firstLive,RootFrameData.live,RootFrameData.write,firstCache,RootFrameData.cache,RootFrameData.atSpan,
      LocalOperands.cachedLayoutFrame,Array.getElem_set,i1,i2,show (2 : Nat) ≠ 1 by decide] using cache2
  have fuelPositive : 0 < options.limits.validation := by
    have budget := input.machine.resources.configuredFuel.2.2.2
    unfold DuplicatePrefixCallSpecification.work at budget
    omega
  obtain ⟨fuel,fuelEq⟩ : ∃ fuel, options.limits.validation = fuel+1 := ⟨options.limits.validation-1,by omega⟩
  have body := RootArgumentsTwo.body options limits remaining span input.machine.settings.debugOff fuel fuelEq frames root firstDone
    (ScopedFrame.entered before tracker .FnEntry) (validatedMachine source)
    (DuplicatePrefixSliceArgument.rawValue (config options remaining span).access.runtime.base argument len ActualReferenceMetadata.reference).imm count
    dead1 cache1 nextDead nextCache input.machine.settings.ghostOff input.machine.settings.shallow rfl input.machine.settings.shallow copy1
  refine ⟨source,validCopied,firstDone,rfl,?_,?_⟩
  · exact (RootEntryFrame.raw_control before (destination place) identity).2.2.2.1
  · exact ScopedFrame.changed_state _ (Storage.withCurrent frames root.frame before)
      (Storage.withCurrent frames (RootArgumentsTwo.result firstDone count).frame (validatedMachine source)) tracker
      ⟨source.base.raw.output.global,.FnEntry⟩ .FnEntry (2,2) input.machine.state.enabled source.installedTracker body

/-- Positive actual root-argument entry constructs its source dictionary from
the fixed original settings and accepts every UInt64 count. Bool destination
protection and execution of the function body are not assumed or asserted. -/
theorem invoke (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState) (argument : DuplicatePrefixSliceArgument.Argument)
    (len : UInt64) (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frames : Array CompilerFrameContext.ActualFrame) (identity : LocalsIdentity)
    (positive : 0 < len.toNat) (count : UInt64) :
    ∃ ctx : Context options remaining span,
    let root := RootFrameData.raw before (destination place) identity input.machine.settings.noDataRace
    let prepared := firstLive root
    ∃ source : ViewedOutcome options remaining span ctx before tracker frames
        (copiedFrame options remaining span prepared.frame 1 (prepared.valid i1) argument len) {} argument len place call data .FnEntry true,
      ∃ validCopied : 1 < (copiedFrame options remaining span prepared.frame 1 (prepared.valid i1) argument len).locals.size,
      ∃ firstDone : RootFrame,
        firstDone.frame = writtenFrame source 1 validCopied ∧
        (RootArgumentsTwo.result firstDone count).frame.returnPlace = destination place ∧
        (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
          (RootCallCore.argumentBody (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
            (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base argument len) (second count))
          (Storage.withCurrent frames root.frame before) =
          .ok (2,2) (Storage.withCurrent frames (RootArgumentsTwo.result firstDone count).frame
            {validatedMachine source with borrowTracker := some ⟨source.base.raw.output.global,tracker.retagMode⟩}) := by
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span
    input.machine.settings.preciseOff input.machine.settings.implicitOff
  exact ⟨ctx,arguments options limits remaining span ctx before tracker argument len place call data input frames identity positive count⟩

end
end DuplicatePrefix.CurrentCallArguments

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallArguments." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved actual current root arguments dependency {dependency}"
