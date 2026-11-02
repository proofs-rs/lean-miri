import empty_function.ProtectionOutcome
import empty_function.CanonicalUnitRetag
import empty_function.UnitRetagObserved

/-! Internal live-branch assembly. Resolve/classify/ensure equations are supplied
by canonical raw-state prefix theorems, never by caller admission predicates. -/
namespace EmptyFunction.LiveProtectionOutcome
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
open EmptyFunction.ProtectionOutcome
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def taggedMachine (before : Machine) (tracker : MachineHooks.BorrowState) (global : GlobalState) : Machine :=
  {before with borrowTracker := some {tracker with global}}

/-- An actual successful entry tag reservation followed by successful source
materialization supplies a total protection outcome, including node exhaustion.
The child constructor itself supplies freshness and concrete-parent evidence. -/
theorem live (s : Static) (metadata : Metadata s) (profile : Profile s)
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
    (stable : Stable before ensuredMachine) : Outcome s place frames frame before := by
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
    right
    refine ⟨borrow,after,protectedResult,?_,?_⟩
    · exact ⟨stable.threads,stable.noRace,stable.ghost,stable.validation,stable.control⟩
    · let changed : InputDraft.Entry := {entry with allocation := entry.allocation.setExtra tree}
      apply ReleaseReady.live (machine := after) (borrow := borrow) ensuredTracker id tag changed enabledAfter rfl
      · exact UnitRetag.replace_lookup ensuredMachine.memory id entry tree
      · exact released
  · left
    refine ⟨.invalidProgram reason,
      LocalUnit.current frames (UnitRetag.registeredFrame frame {} id tag)
        {ensuredMachine with memory := UnitRetag.replaceTree ensuredMachine.memory id entry tree},?_,rfl⟩
    exact UnitRetagResult.protect_of_failed_reborrow s.cfg.retag s.limits.retag place
      (LocalUnit.current frames frame before) tracker global tag (fields.size place layout)
      enabled tagged (.invalidProgram reason) _ failed

open Lean Elab Command in
run_cmd do
  for name in #[``taggedMachine,``live] do
    for dependency in (← collectAxioms name) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved live protection outcome axiom {dependency} in {name}"
#print axioms live
end EmptyFunction.LiveProtectionOutcome
