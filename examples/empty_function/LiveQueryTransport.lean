import empty_function.LiveProtectionSnapshot
import empty_function.ProjectionSnapshot
import empty_function.ProjectedIndirectPreflight
namespace EmptyFunction.LiveQueryTransport
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
open EmptyFunction.ProtectionOutcome EmptyFunction.LiveProtectionOutcome
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem query (s : Static) (metadata : Metadata s) (profile : Profile s)
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
      (LocalUnit.current frames frame before) = .ok () afterState)
    (old : MemPlace Provenance) (amount : Size)
    (queryAtEnsured : EvalProjectionMachine.memoryOffset (ConcreteProtection.source s).pointers
      (LocalUnit.current frames (UnitRetag.registeredFrame frame {} id tag) ensuredMachine)
      old amount .inbounds .none = .ok (ProjectedIndirectPreflight.shifted old amount)) :
    EvalProjectionMachine.memoryOffset (ConcreteProtection.source s).pointers afterState
      old amount .inbounds .none = .ok (ProjectedIndirectPreflight.shifted old amount) := by
  obtain ⟨tree,exactState⟩ := LiveProtectionSnapshot.of_success s metadata profile place frames frame before
    tracker global tag layout noMetadata aligned enabled frameBorrow tagged id offset parent resolve info
    classification data ensuredMachine ensuredTracker ensured entry live currentTag formed enabledAfter afterState success
  rw [exactState]
  rw [ProjectionSnapshot.offset_congr (ConcreteProtection.source s).pointers
    (LocalUnit.current frames (UnitRetag.registeredFrame frame {} id tag) ensuredMachine)
    (LocalUnit.current frames (UnitRetag.registeredFrame frame {} id tag)
      {ensuredMachine with memory := UnitRetag.replaceTree ensuredMachine.memory id entry tree}) rfl
    (ProjectionSnapshot.replace_info ensuredMachine.memory id entry tree live)
    (ProjectionSnapshot.replace_live ensuredMachine.memory id entry tree live)]
  exact queryAtEnsured

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``query) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved live query transport axiom {dependency}"
#print axioms query
end EmptyFunction.LiveQueryTransport
