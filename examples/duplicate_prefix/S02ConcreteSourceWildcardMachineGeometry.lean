import duplicate_prefix.S02ConcreteSourceWildcardInstalled
import duplicate_prefix.S02ConcreteSourceWildcardSharedGeometry
import duplicate_prefix.S02SeparateDestinationTickLedger

namespace DuplicatePrefix.S02ConcreteSourceWildcardMachineGeometry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- The same real positive call with a wildcard return has the physical
settings used by the Default and copy helpers. -/
theorem after_exact
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (tracker : MachineHooks.BorrowState)
      (installed : CompilerFrameContext.ActualFrame)
      (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] installed post) ∧
      post.borrowTracker = some tracker ∧ tracker.retagMode = .Default ∧
      post.user.payload.ghost = false ∧ post.user.payload.validation = .Shallow ∧
      ((config options (remaining+1) span).terminators.getControl post.user).checkedArithmetic = false ∧
      ((config options (remaining+1) span).terminators.getControl post.user).gcInterval = 0 ∧
      post.threads.fixedScheduling = true ∧ post.dataRace = none ∧
      post.user.addresses = before.user.addresses ∧
      post.user.payload.payload.user.types = before.user.payload.payload.user.types ∧
      post.user.payload.payload.user.backend = .none ∧
      ∃ thread, post.threads.activeThread? = some thread ∧ thread.topUserRelevantFrame = some 0 := by
  obtain ⟨reference,firstFresh,destination,secondFresh,tree,updated,actual,destId,_packet⟩ :=
    S02ConcreteSourceWildcardInstalled.enters id tag address len count input nonempty different returnWildcard
  let current := GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
    reference.tracker firstFresh reference.id reference.entry tag reference.offset len
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
  let frame := (RootArgumentsTwo.result
    (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
      reference.id reference.tracker.global.nextPointerTag) count).frame
  let changed := {frame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id
    destination.tracker.global.nextPointerTag
  let installed := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
  let tracker := TypedBorrowSteps.registeredTracker
    (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
    destination.tracker.global.nextPointerTag
  obtain ⟨settings⟩ := S02ConcreteSourceWildcardControl.at_protection_any_count
    id tag address len count input reference firstFresh destination destId secondFresh tree updated
  have tracked : after.machine.borrowTracker = some tracker := rfl
  have trackerEq : settings.tracker = tracker := Option.some.inj (settings.enabled.symm.trans tracked)
  have mode : tracker.retagMode = .Default := by rw [←trackerEq]; exact settings.mode
  obtain ⟨tickAddresses,tickTypes,tickBackend,tickGhost,tickShallow,tickUnchecked,
    tickNoGc,tickFixed,tickRace,thread,tickActive,topZero⟩ :=
    S02ConcreteSourceWildcardSharedGeometry.after_tick id tag address len count input
      reference firstFresh destination destId secondFresh tree updated
  obtain ⟨_mem,_borrow,raceEq,threadEq,addressesEq,backendEq,_extras⟩ :=
    RootZeroInvocationState.tick_fields options remaining span after.machine
  have typeEq : (RootZeroCompleteState.tick options remaining span after.machine).user.payload.payload.user.types =
      after.machine.user.payload.payload.user.types :=
    (S02SeparateDestinationTickLedger.preserved options remaining span after.machine).2.2.2.2.2.1
  refine ⟨reference,tracker,installed,after.machine,actual,tracked,mode,settings.ghost,
    settings.shallow,settings.unchecked,settings.noGc,settings.fixed,settings.race,
    ?_,?_,settings.backend,?_⟩
  · exact addressesEq.symm.trans tickAddresses
  · exact typeEq.symm.trans tickTypes
  · exact ⟨thread,by rw [←threadEq]; exact tickActive,topZero⟩

end
end DuplicatePrefix.S02ConcreteSourceWildcardMachineGeometry

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceWildcardMachineGeometry.after_exact) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source wildcard machine geometry dependency {dependency}"
