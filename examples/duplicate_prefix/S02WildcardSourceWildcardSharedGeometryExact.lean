import duplicate_prefix.S02WildcardSourceWildcardControl
import duplicate_prefix.RootZeroInvocationState

namespace DuplicatePrefix.S02WildcardSourceWildcardSharedGeometryExact
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Wildcard return provenance does not affect the source-side shared Ref/len
site geometry through the first pure-prefix accounting tick. -/
theorem after_tick
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new .wildcard (Size.ofBytes address)) len)
    (output : GeneralBorrowForestFnEntry.Output)
    (firstFresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615)
    (destination : DuplicatePrefixReturnPlaceInput.Input
      (GeneralBorrowRawWildcardWindowFunctionScope.resultMachine (RawRootInvocation.machine #[] before)
        reference.tracker firstFresh reference.id reference.entry output.child.tree) place)
    (destinationId : destination.id = input.contract.destination.id)
    (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
    (tree : BorrowTree) (updated : Allocation Provenance BorrowTree) :
    let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine (RawRootInvocation.machine #[] before)
      reference.tracker firstFresh reference.id reference.entry output.child.tree
    let root := RawRootInvocation.root before place input.contract.model.noDataRace
    let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
        (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
    let frame := (RootArgumentsTwo.result
      (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
        reference.id reference.tracker.global.nextPointerTag) count).frame
    let changed := {frame with location := .unwinding ⟨601⟩}
    let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
    let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
    let machine := RootZeroCompleteState.tick options remaining span after.machine
    machine.user.addresses = before.user.addresses ∧
    machine.user.payload.payload.user.types = before.user.payload.payload.user.types ∧
    machine.user.payload.payload.user.backend = .none ∧
    machine.user.payload.ghost = false ∧ machine.user.payload.validation = .Shallow ∧
    ((config options (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false ∧
    ((config options (remaining+1) span).terminators.getControl machine.user).gcInterval = 0 ∧
    machine.threads.fixedScheduling = true ∧ machine.dataRace = none ∧
    ∃ thread, machine.threads.activeThread? = some thread ∧ thread.topUserRelevantFrame = some 0 := by
  let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine (RawRootInvocation.machine #[] before)
    reference.tracker firstFresh reference.id reference.entry output.child.tree
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
  let frame := (RootArgumentsTwo.result
    (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
      reference.id reference.tracker.global.nextPointerTag) count).frame
  let changed := {frame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  obtain ⟨settings⟩ := S02WildcardSourceWildcardControl.at_protection
    address len count input reference output firstFresh destination destinationId secondFresh tree updated
  obtain ⟨_,_,raceEq,addressEq,ghostEq,shallowEq,typesEq,backendEq,_⟩ :=
    RawRootInvocation.preservation #[] before
  have afterUser : after.machine.user = (RawRootInvocation.machine #[] before).user := rfl
  have afterThreads : after.machine.threads = (RawRootInvocation.machine #[] before).threads := rfl
  have addresses : after.machine.user.addresses = before.user.addresses := by
    rw [afterUser]; exact addressEq
  have types : after.machine.user.payload.payload.user.types = before.user.payload.payload.user.types := by
    rw [afterUser]; exact typesEq
  let machine := RootZeroCompleteState.tick options remaining span after.machine
  obtain ⟨_memory,_borrow,tickRace,tickThreads,tickAddresses,tickBackend,_extras⟩ :=
    RootZeroInvocationState.tick_fields options remaining span after.machine
  refine ⟨tickAddresses.trans addresses,?_,tickBackend.trans settings.backend,?_,?_,?_,?_,
    tickThreads ▸ settings.fixed,tickRace ▸ settings.race,?_⟩
  · change machine.user.payload.payload.user.types = _
    dsimp only [machine]
    unfold RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact types
  · rw [RootZeroCompleteState.tick_ghost]; exact settings.ghost
  · rw [RootZeroCompleteState.tick_shallow]; exact settings.shallow
  · exact (RootZeroCompleteState.tick_flags options remaining span after.machine).1.trans settings.unchecked
  · exact (RootZeroCompleteState.tick_flags options remaining span after.machine).2.trans settings.noGc
  · have rawActive : (RawRootInvocation.machine #[] before).threads.activeThread? =
        some {input.contract.thread with topUserRelevantFrame := some 0} := by
      change (CallEntryFacts.cacheTop (CallEntryFacts.freshRoot before).1 0).threads.activeThread? = _
      exact AsMutPushPreserves.active_cache (CallEntryFacts.freshRoot before).1 input.contract.thread
        (by simpa only [CallEntryFacts.freshRoot] using input.contract.active) 0
    have threadEq : settings.thread = {input.contract.thread with topUserRelevantFrame := some 0} := by
      have h := settings.active
      change after.machine.threads.activeThread? = some settings.thread at h
      rw [afterThreads] at h
      exact Option.some.inj (h.symm.trans rawActive)
    exact ⟨settings.thread,by rw [tickThreads]; exact settings.active,by rw [threadEq]⟩

end
end DuplicatePrefix.S02WildcardSourceWildcardSharedGeometryExact

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSourceWildcardSharedGeometryExact.after_tick) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source wildcard shared-geometry dependency {dependency}"
