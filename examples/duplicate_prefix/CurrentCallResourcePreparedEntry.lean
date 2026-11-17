import duplicate_prefix.CurrentCallResourceEntryBody
import duplicate_prefix.CurrentCallPreparedResources

namespace DuplicatePrefix.CurrentCallResourcePreparedEntry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallResourceEntryBody
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
noncomputable section

/-- Actual fresh-identity/relevance updates preserve the selected model. -/
theorem model {options remaining span before}
    (M : DuplicatePrefixCallModel.Model options remaining span before)
    (frames : Array CompilerFrameContext.ActualFrame) :
    DuplicatePrefixCallModel.Model options remaining span (CurrentCallPush.preparedMachine before frames) := by
  have controlEq :
      (PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
        (CurrentCallPush.preparedMachine before frames).user =
      (PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user := by
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  exact ⟨M.debugOff,M.preciseOff,M.implicitOff,M.ghostOff,M.shallow,M.defaultTracker,M.noDataRace,
    M.noBackend,M.metadata,M.fixedScheduler,by rw [controlEq];exact M.unchecked,
    by rw [controlEq];exact M.noGc,M.nullComparator,M.sourceMatches⟩

/-- The same actual Bool storage and pointer in the post-push world. -/
def physical {before place}
    (P : CandidateCurrentBoolUninitWrite.PhysicalWindow before place)
    (frames : Array CompilerFrameContext.ActualFrame) :
    CandidateCurrentBoolUninitWrite.PhysicalWindow (CurrentCallPush.preparedMachine before frames) place where
  pointer := P.pointer
  physicalPointer := P.physicalPointer
  layout := P.layout
  aligned := P.aligned
  id := P.id
  entry := P.entry
  base := P.base
  offset := P.offset
  capacity := P.capacity
  live := P.live
  cachedBase := P.cachedBase
  pointerAddress := P.pointerAddress
  bounds := P.bounds
  size := P.size
  bytes := P.bytes
  mutable := P.mutable
  maskValid := P.maskValid
  maskLength := P.maskLength
  provenanceMap := P.provenanceMap

/-- Pure actual raw-push prefix transport. The original root and every resource
family remain exact; no new condition, operation result, or denotation is added. -/
def prepared {options remaining span frames root before tracker data owner id offset len W place}
    (C : Conditions options remaining span frames root before tracker data owner id offset len W place) :
    Conditions options remaining span frames root (CurrentCallPush.preparedMachine before frames)
      tracker data owner id offset len (CurrentCallPreparedResources.prepared W frames) place where
  model := model C.model frames
  state := CurrentCallPreparedResources.state C.state frames
  highwater := CurrentCallPreparedResources.highwater C.highwater frames
  rawLocals := C.rawLocals
  borrowFrame := C.borrowFrame
  frameBorrow := C.frameBorrow
  binding := CurrentCallPreparedResources.windowBinding C.binding frames
  positive := C.positive
  signedFits := C.signedFits
  tagRoom := C.tagRoom
  sourceShort := C.sourceShort
  dynamicFuel := C.dynamicFuel
  validationFuel := C.validationFuel
  dynamicEq := C.dynamicEq
  validationEq := C.validationEq
  origins := C.origins
  physical := physical C.physical frames
  returnOwner := C.returnOwner
  V := CurrentCallPreparedResources.prepared C.V frames
  returnPointer := C.returnPointer
  returnBinding := CurrentCallPreparedResources.windowBinding C.returnBinding frames
  ready := C.ready
  boolRoom := C.boolRoom
  sameAllocation := C.sameAllocation
  sameCompletion := C.sameCompletion
  separate := C.separate

@[simp] theorem prepared_physical_id {options remaining span frames root before tracker data owner id offset len W place}
    (C : Conditions options remaining span frames root before tracker data owner id offset len W place) :
    (prepared C).physical.id = C.physical.id := rfl
@[simp] theorem prepared_physical_pointer {options remaining span frames root before tracker data owner id offset len W place}
    (C : Conditions options remaining span frames root before tracker data owner id offset len W place) :
    (prepared C).physical.pointer = C.physical.pointer := rfl
@[simp] theorem prepared_physical_offset {options remaining span frames root before tracker data owner id offset len W place}
    (C : Conditions options remaining span frames root before tracker data owner id offset len W place) :
    (prepared C).physical.offset = C.physical.offset := rfl
@[simp] theorem prepared_physical_entry {options remaining span frames root before tracker data owner id offset len W place}
    (C : Conditions options remaining span frames root before tracker data owner id offset len W place) :
    (prepared C).physical.entry = C.physical.entry := rfl
@[simp] theorem prepared_return_loan {options remaining span frames root before tracker data owner id offset len W place}
    (C : Conditions options remaining span frames root before tracker data owner id offset len W place) :
    (prepared C).V.loan = C.V.loan := rfl
@[simp] theorem prepared_return_pointer {options remaining span frames root before tracker data owner id offset len W place}
    (C : Conditions options remaining span frames root before tracker data owner id offset len W place) :
    (prepared C).V.pointer = C.V.pointer := rfl
@[simp] theorem prepared_return_allocation {options remaining span frames root before tracker data owner id offset len W place}
    (C : Conditions options remaining span frames root before tracker data owner id offset len W place) :
    (prepared C).V.allocation = C.V.allocation := rfl
@[simp] theorem prepared_return_precise {options remaining span frames root before tracker data owner id offset len W place}
    (C : Conditions options remaining span frames root before tracker data owner id offset len W place) :
    (prepared C).V.precise = C.V.precise := rfl

end
end DuplicatePrefix.CurrentCallResourcePreparedEntry
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallResourcePreparedEntry.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved prepared entry dependency {dependency}"
