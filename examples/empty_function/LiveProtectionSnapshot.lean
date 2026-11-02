import empty_function.LiveProtectionOutcome

namespace EmptyFunction.LiveProtectionSnapshot
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
open EmptyFunction.ProtectionOutcome EmptyFunction.LiveProtectionOutcome
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Actual successful unit protection exposes its concrete tree writeback.
The source ensure equation is an internal assembly edge. -/
theorem of_success (s : Static) (metadata : Metadata s) (profile : Profile s)
    (place : MPlaceTy Provenance) (frames : Array LocalUnit.F) (frame : LocalUnit.F)
    (before : Machine) (tracker : MachineHooks.BorrowState) (global : GlobalState) (tag : BorTag)
    (layout : place.layout = s.abi.ret.layout)
    (noMetadata : place.mplace.metadata = .none) (aligned : place.mplace.misaligned = none)
    (enabled : before.borrowTracker = some tracker)
    (frameBorrow : frame.extra.borrowTracker = some {})
    (tagged : tracker.global.newPointerTag = .ok (global,tag))
    (id : AllocId) (offset : UInt64) (parent : ProvenanceExtra)
    (resolve : s.cfg.retag.resolveAllocation place.mplace.ptr
      (LocalUnit.current frames frame (taggedMachine before tracker global)) =
      .ok (some ⟨id,Size.ofBytes offset,parent⟩)
        (LocalUnit.current frames frame (taggedMachine before tracker global)))
    (info : AllocationInfo) (classification : before.memory.getAllocInfo id = .ok info)
    (data : info.kind = .liveData)
    (ensuredMachine : Machine) (ensuredTracker : MachineHooks.BorrowState)
    (ensured : s.cfg.retag.ensureTreeExtra id
      (LocalUnit.current frames (UnitRetag.registeredFrame frame {} id tag)
        (UnitRetag.registeredMachine (taggedMachine before tracker global) {tracker with global} tag)) =
      .ok () (LocalUnit.current frames (UnitRetag.registeredFrame frame {} id tag) ensuredMachine))
    (entry : InputDraft.Entry)
    (live : ensuredMachine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (currentTag : BorTag) (formed : Nonempty (TreeRuntimeInput.TreeFormed entry.allocation.extra currentTag))
    (enabledAfter : ensuredMachine.borrowTracker = some ensuredTracker)
    (afterState : State)
    (success : TypedRetag.protectInPlaceFunctionArgument s.cfg.retag s.limits.retag place
      (LocalUnit.current frames frame before) = .ok () afterState) :
    ∃ tree, afterState = LocalUnit.current frames (UnitRetag.registeredFrame frame {} id tag)
      {ensuredMachine with memory := UnitRetag.replaceTree ensuredMachine.memory id entry tree} := by
  have fields := CanonicalUnitRetag.fields s metadata profile
  have tagEnabled : (taggedMachine before tracker global).borrowTracker = some {tracker with global} := rfl
  obtain ⟨formed⟩ := formed
  have outcomes := UnitRetagObserved.reborrow_zero_live_cases s.cfg.retag s.limits.retag place
    frames frame {} (taggedMachine before tracker global) {tracker with global} tagEnabled frameBorrow
    id entry offset parent tag (fields.check _ _) resolve fields.log fields.precise (fields.freeze place layout)
    info classification data ensuredMachine ensured live currentTag formed ensuredTracker.global.protectedTags
  rcases outcomes with ⟨tree,borrowed,released,rights⟩ | ⟨reason,tree,failed⟩
  · let after : Machine := {ensuredMachine with memory := UnitRetag.replaceTree ensuredMachine.memory id entry tree}
    let borrow : FrameState := ({} : FrameState).addProtector id tag
    have protectedResult := UnitRetagResult.protect_of_returned_reborrow s.cfg.retag s.limits.retag place
      (LocalUnit.current frames frame before) tracker global tag (fields.size place layout)
      enabled tagged (some (.concrete id tag))
      (LocalUnit.current frames (UnitRetag.registeredFrame frame {} id tag) after)
      (LocalUnit.current frames (UnitRetag.registeredFrame frame {} id tag) after)
      borrowed (by intro _; simp) (fields.write place _ layout noMetadata aligned _)
    have same : afterState = LocalUnit.current frames (UnitRetag.registeredFrame frame {} id tag) after := by
      have equation := success.symm.trans protectedResult
      injection equation
    exact ⟨tree,same⟩
  · have failedResult := UnitRetagResult.protect_of_failed_reborrow s.cfg.retag s.limits.retag place
      (LocalUnit.current frames frame before) tracker global tag (fields.size place layout)
      enabled tagged (.invalidProgram reason) _ failed
    rw [success] at failedResult
    cases failedResult

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``of_success) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved actual live snapshot axiom {dependency}"
#print axioms of_success
end EmptyFunction.LiveProtectionSnapshot
