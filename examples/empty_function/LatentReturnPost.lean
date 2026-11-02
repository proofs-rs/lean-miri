import empty_function.CanonicalLatentProtect
import empty_function.ReturnSingleton
namespace EmptyFunction.LatentReturnPost
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Configuration UnitRetag
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-- The lazy source's real singleton certificate closes the actual pop after
body execution. The current root cache and counter are retained on release. -/
theorem pop (s : Static)
    (globals : GlobalAllocationHooks Provenance BorrowTree MiriMemoryKind
      (PlaceMachine.AccessState MiriMemoryKind RootUser))
    (binding : s.cfg.retag.ensureTreeExtra = GlobalAllocationMachine.ensure .global globals)
    (synchronize : ∀ memory view, globals.synchronizeMemory memory view = {view with machine := {view.machine with memory}})
    (frames : Array LocalUnit.F) (frame : LocalUnit.F) (machine : ChoiceExecution.S)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (protections : ProtectedTags) (tag : BorTag) (fresh : protections.get tag = none)
    (protectedEq : tracker.global.protectedTags = protections.insert tag .StrongProtector)
    (id : AllocId) (entry : InputDraft.Entry) (tree : BorrowTree)
    (released : tree.releaseProtector tag tracker.global.protectedTags = ⟨tree,.Released⟩)
    (thread : Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread) :
    let protectedFrame := registeredFrame frame {} id tag
    let baselineTracker := {tracker with global := {tracker.global with protectedTags := protections}}
    let after := {machine with borrowTracker := some baselineTracker, memory := replaceTree machine.memory id entry tree}
    (ReturnStep.control s).popFrame ()
      (LocalUnit.current frames protectedFrame {machine with memory := replaceTree machine.memory id entry tree}) =
      ((⟨⟨frames⟩,FrameExit.afterRelevanceAt frames protectedFrame after
        (thread.topUserRelevantFrame.getD frames.size)⟩ : State),.ok protectedFrame) := by
  dsimp only
  let protectedFrame := registeredFrame frame {} id tag
  let baselineTracker := {tracker with global := {tracker.global with protectedTags := protections}}
  let after := {machine with borrowTracker := some baselineTracker, memory := replaceTree machine.memory id entry tree}
  have releaseEq := LatentProtectionPost.release_after_ensure .global globals synchronize frames frame machine
    tracker enabled protections tag fresh protectedEq id entry tree released
  rw [←binding] at releaseEq
  change MachineHooks.beforeStackPopWithEnsure s.cfg.retag.ensureTreeExtra
    (LocalUnit.current frames protectedFrame {machine with memory := replaceTree machine.memory id entry tree}) =
      .ok () (LocalUnit.current frames protectedFrame after) at releaseEq
  have activeAfter : after.threads.activeThread? = some thread := active
  have relevant := FrameExit.relevance_before_pop frames protectedFrame after thread activeAfter
  change MachineHooks.run (TypedMachineBindings.popRaw
    (TypedMachineBindings.retagHooks s.cfg.access s.cfg.retag)) _ = _
  unfold TypedMachineBindings.popRaw
  simp only [TypedMachineBindings.retagHooks,MachineHooks.run,Call.run,bind,Bind.bind,EStateM.bind]
  rw [releaseEq]
  simp only [LocalUnit.current,FrameExit.withCurrent,protectedFrame,after,baselineTracker] at relevant ⊢
  rw [relevant]
  simp [LocalUnit.current,FrameExit.withCurrent,protectedFrame,after,baselineTracker,Stack.popFrame,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,
    set,MonadStateOf.set,EStateM.set,pure,Pure.pure,EStateM.pure,Except.pure]
end EmptyFunction.LatentReturnPost
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.LatentReturnPost." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved latent return axiom {dependency} in {name}"
