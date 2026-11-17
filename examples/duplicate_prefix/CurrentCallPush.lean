import duplicate_prefix.CurrentCallArguments

/-! Actual fresh-root/push prefix. Stack readiness is execution representation,
separate from Freeze ownership: an active actor and a cache index valid AFTER
push are needed by the source relevance hook. No startup is invented. -/
namespace DuplicatePrefix.CurrentCallPush
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall
open CanonicalConfigFacts ActualReferenceContext CallEntryFacts
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Operational post-push cache readiness, not a successful push certificate.
For an empty incoming stack it permits None OR some 0; None is not asserted
operationally necessary. Valid cached caller frames are allowed in larger stacks. -/
def StackReadiness (before : Before) (frames : Array CompilerFrameContext.ActualFrame) : Prop :=
  ∃ thread, before.threads.activeThread? = some thread ∧
    ∀ index, thread.topUserRelevantFrame = some index → index < frames.size+1

/-- Empty-stack readiness still permits the operational some-zero cache case. -/
theorem readiness_empty (before : Before) : StackReadiness before #[] ↔
    ∃ thread, before.threads.activeThread? = some thread ∧
      (thread.topUserRelevantFrame = none ∨ thread.topUserRelevantFrame = some 0) := by
  constructor
  · rintro ⟨thread,active,bound⟩
    refine ⟨thread,active,?_⟩
    cases cached : thread.topUserRelevantFrame with
    | none => exact Or.inl rfl
    | some index =>
      have small := bound index cached
      have zero : index = 0 := by simpa using small
      subst index
      exact Or.inr rfl
  · rintro ⟨thread,active,cached⟩
    refine ⟨thread,active,?_⟩
    intro index atIndex
    rcases cached with absent | zero
    · simp [absent] at atIndex
    · simp [zero] at atIndex
      subst index
      decide

private theorem relevance_max (value : UInt8) : value ≤ (255 : UInt8) := by
  apply UInt8.le_iff_toNat_le.mpr
  have bound := value.toNat_lt
  change value.toNat ≤ 255
  omega

/-- Root relevance 255 dominates every cached frame's UInt8 relevance. The
source hook therefore installs the new top, with no empty-cache restriction. -/
theorem relevance_after_push (frames : Array CompilerFrameContext.ActualFrame)
    (frame : CompilerFrameContext.ActualFrame) (before : Before)
    (thread : Miri.Concurrency.ThreadRecord)
    (active : before.threads.activeThread? = some thread)
    (maximum : frame.extra.userRelevance = 255)
    (cacheBound : ∀ index, thread.topUserRelevantFrame = some index → index < frames.size+1) :
    FrameRelevance.afterStackPush false (Storage.withCurrent frames frame before) =
      .ok () (Storage.withCurrent frames frame (cacheTop before frames.size)) := by
  unfold FrameRelevance.afterStackPush
  unfold_relevance_helpers
  cases cached : thread.topUserRelevantFrame with
  | none =>
    simp [MachineHooks.currentFrame,Storage.withCurrent,Stack.currentFrame?,Array.back?_push,
      active,cached,FrameRelevance.top,maximum,bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,
      modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,pure,EStateM.pure,cacheTop]
  | some index =>
    have valid : index < (frames.push frame).size := by simpa using cacheBound index cached
    have dominates : (frames.push frame)[index].extra.userRelevance ≤ frame.extra.userRelevance := by
      rw [maximum]
      exact relevance_max _
    simp [MachineHooks.currentFrame,Storage.withCurrent,Stack.currentFrame?,Array.back?_push,
      active,cached,FrameRelevance.top,Array.getElem?_eq_getElem valid,dominates,bind,EStateM.bind,get,getThe,
      MonadStateOf.get,EStateM.get,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,pure,EStateM.pure,cacheTop]

/-- The actual lifecycle fresh identity allocation and raw root push. Only the
source actor/cache readiness is added to the selected fixed configuration. -/
theorem push (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits) (debugOff : options.place.debugAssertions = false)
    (before : Before) (frames : Array CompilerFrameContext.ActualFrame) (destination : RuntimeStackPlace Provenance)
    (ready : StackReadiness before frames) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).pushRaw ()
      RootBody.reflected.functionInstance RootBody.reflected.body destination (.stop true) (⟨⟨frames⟩,before⟩ : RootState) =
      .ok () (rawPushedState frames before destination) := by
  obtain ⟨thread,active,cacheBound⟩ := ready
  change CallMachine.pushRaw (CallEntryFacts.config options () remaining span).lifecycle
    (CallEntryFacts.config options () remaining span).compiler.debugAssertions
    RootBody.reflected.functionInstance RootBody.reflected.body destination (.stop true) _ = _
  have debug := (CanonicalConfigFacts.actual_fields options () remaining span).debug
  unfold CallEntryFacts.config at debug ⊢
  rw [debug,debugOff]
  unfold CallMachine.pushRaw
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  rw [fields.freshLocalsIdentity,fields.preambleSpan,fields.frameCompiler,fields.requiredConstants]
  simp only [Bool.false_and,Bool.false_eq_true,ite_false,bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,
    set,MonadStateOf.set,EStateM.set,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
  rw [root_preamble_span]
  dsimp only
  rw [init_root_frame]
  dsimp only
  let fresh := freshRoot before
  have checks := root_required_constants frames (rawRootFrame fresh.1 destination fresh.2) fresh.1 rfl rfl
  dsimp only [fresh,freshRoot,Storage.withCurrent] at checks
  rw [checks]
  simpa only [rawPushedState,fresh,freshRoot,Storage.withCurrent] using
    relevance_after_push frames (rawRootFrame fresh.1 destination fresh.2) fresh.1 thread active rfl cacheBound

/-- Exact non-memory updates made by the raw push prefix. -/
def preparedMachine (before : Before) (frames : Array CompilerFrameContext.ActualFrame) : Before :=
  cacheTop (freshRoot before).1 frames.size

/-- Identity allocation and relevance caching leave the current-call resource,
physical-storage and selected configuration clauses intact. -/
theorem prepared_input {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frames : Array CompilerFrameContext.ActualFrame) :
    CurrentCallAdmission.Proposed options limits remaining span (preparedMachine before frames)
      tracker argument len place call data := by
  rcases input with ⟨contents, actual, machine⟩
  rcases contents with ⟨distinct, source, ret, compatible, grants⟩
  rcases actual with ⟨protectors, length, copies, instances, sourceArgument, returnPlace,
    sourceAddress, returnAddress, sourceValue, returnValue, aligned⟩
  rcases machine with ⟨worldIds, completionIds, completed, cacheOrigins, state, settings, resources⟩
  rcases state with ⟨state, parentTags⟩
  rcases state with ⟨enabled, allocationIds, cachedRootIds, cachedRootTags, tags, formed,
    roots, coherent, possible, byteLength, maskValid, maskLength, provenance, treeLength⟩
  rcases settings with ⟨debugOff, preciseOff, implicitOff, ghostOff, shallow, defaultTracker,
    noDataRace, noBackend, metadata, fixedScheduler, unchecked, noGc, nullComparator, sourceMatches⟩
  rcases resources with ⟨remainingFuel, executionFuel, configuredFuel, dynamicFuel, compatibility,
    tagRoom, tagsBelow, cachedRootsBelow, nodeRoom, storageRoom, globalRoom, initializerRoom⟩
  have controlEq :
      (PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
        (preparedMachine before frames).user =
      (PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user := by
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  rw [← controlEq] at unchecked noGc
  exact ⟨⟨distinct, source, ret, compatible, grants⟩,
    ⟨protectors, length, copies, instances, sourceArgument, returnPlace, sourceAddress,
      returnAddress, sourceValue, returnValue, aligned⟩,
    ⟨worldIds, completionIds, completed, cacheOrigins,
      ⟨⟨enabled, allocationIds, cachedRootIds, cachedRootTags, tags, formed, roots, coherent,
        possible, byteLength, maskValid, maskLength, provenance, treeLength⟩, parentTags⟩,
      ⟨debugOff, preciseOff, implicitOff, ghostOff, shallow, defaultTracker, noDataRace,
        noBackend, metadata, fixedScheduler, unchecked, noGc, nullComparator, sourceMatches⟩,
      ⟨remainingFuel, executionFuel, configuredFuel, dynamicFuel, compatibility, tagRoom,
        tagsBelow, cachedRootsBelow, nodeRoom, storageRoom, globalRoom, initializerRoom⟩⟩⟩

/-- Actual push followed by both argument copies under one FnEntry scope. The
fresh locals token is allocated by the source prefix, never supplied externally.
This remains a prefix: return protection and the rest of initStackFrame follow. -/
theorem arguments (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : Context options remaining span) (before : Before) (tracker : MachineHooks.BorrowState)
    (argument : DuplicatePrefixSliceArgument.Argument) (len : UInt64) (place : MPlaceTy Provenance)
    (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frames : Array CompilerFrameContext.ActualFrame) (ready : StackReadiness before frames)
    (positive : 0 < len.toNat) (count : UInt64) :
    let machine := preparedMachine before frames
    let transported := prepared_input input frames
    let root := RootFrameData.raw machine (CurrentCallArguments.destination place) (freshRoot before).2 transported.machine.settings.noDataRace
    let prepared := EmptyRootArguments.firstLive root
    ∃ source : CurrentCallReferenceEntry.ViewedOutcome options remaining span ctx machine tracker frames
        (CurrentCallReferenceEntry.copiedFrame options remaining span prepared.frame 1 (prepared.valid EmptyRootArguments.i1) argument len)
        {} argument len place call data .FnEntry true,
      ∃ validCopied : 1 < (CurrentCallReferenceEntry.copiedFrame options remaining span prepared.frame 1
          (prepared.valid EmptyRootArguments.i1) argument len).locals.size,
      ∃ firstDone : RootFrameData.RootFrame,
        firstDone.frame = CurrentCallReferenceEntry.writtenFrame source 1 validCopied ∧
        (RootArgumentsTwo.result firstDone count).frame.returnPlace = CurrentCallArguments.destination place ∧
        (do
          let hooks := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
          hooks.pushRaw () RootBody.reflected.functionInstance RootBody.reflected.body
            (CurrentCallArguments.destination place) (.stop true)
          hooks.withRetagMode () .FnEntry (RootCallCore.argumentBody hooks
            (DuplicatePrefixSliceArgument.first (ActualReferenceContext.config options remaining span).access.runtime.base argument len)
            (EmptyRootArguments.second count))) (⟨⟨frames⟩,before⟩ : RootState) =
          .ok (2,2) (Storage.withCurrent frames (RootArgumentsTwo.result firstDone count).frame
            {CurrentCallReferenceEntry.validatedMachine source with borrowTracker := some ⟨source.base.raw.output.global,tracker.retagMode⟩}) := by
  let machine := preparedMachine before frames
  let transported := prepared_input input frames
  obtain ⟨source, validCopied, firstDone, frameEq, returnEq, body⟩ :=
    CurrentCallArguments.arguments options limits remaining span ctx machine tracker argument len place call data
      transported frames (freshRoot before).2 positive count
  refine ⟨source,validCopied,firstDone,frameEq,returnEq,?_⟩
  have pushed := push options (remaining+1) span limits input.machine.settings.debugOff before frames
    (CurrentCallArguments.destination place) ready
  simp only [bind,EStateM.bind]
  rw [pushed]
  exact body

end
end DuplicatePrefix.CurrentCallPush

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallPush." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved actual current push dependency {dependency}"
