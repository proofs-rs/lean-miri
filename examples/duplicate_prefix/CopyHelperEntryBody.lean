import duplicate_prefix.CopyHelperSteps
import duplicate_prefix.CopyHelperCleanup
namespace DuplicatePrefix.CopyHelperEntryBody
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem actual_two_live
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (location : frame.location = .mir ⟨0,0⟩)
    (valid4 : (4 : MIR.LocalId) < frame.locals.size)
    (valid5 : (5 : MIR.LocalId) < frame.locals.size)
    (dead4 : frame.locals[4].value = .dead) (dead5 : frame.locals[5].value = .dead)
    (noClocks : frame.extra.dataRace = none) (allImmediate : CopyHelperCleanup.AllImmediate frame) :
    let config := PreparedContracts.actualConfig options () remaining span
    ∃ first done : CompilerFrameContext.ActualFrame,
      ExecutionMachine.step config limits () (Storage.withCurrent frames frame machine) =
        (Storage.withCurrent frames first machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent frames first machine) =
        (Storage.withCurrent frames done machine,.ok true) ∧
      done.body = frame.body ∧ done.bodyIdentity = frame.bodyIdentity ∧ done.functionInstance = frame.functionInstance ∧
      done.extra = frame.extra ∧ done.returnPlace = frame.returnPlace ∧ done.returnContinuation = frame.returnContinuation ∧
      done.vaList = frame.vaList ∧ done.localsIdentity = frame.localsIdentity ∧ done.locals.size = frame.locals.size ∧
      done.location = .mir ⟨0,2⟩ ∧ done.locals[0]? = frame.locals[0]? ∧
      (done.locals[4]?.map (·.value)) = some (.live (.immediate .uninit)) ∧
      (done.locals[5]?.map (·.value)) = some (.live (.immediate .uninit)) ∧
      CopyHelperCleanup.AllImmediate done := by
  let config := PreparedContracts.actualConfig options () remaining span
  let first := SourceSteps.liveFrame frame ⟨0,0⟩ 4 valid4
  have valid5First : (5 : MIR.LocalId) < first.locals.size := by simpa [first,SourceSteps.liveFrame] using valid5
  let done := SourceSteps.liveFrame first ⟨0,1⟩ 5 valid5First
  have firstStep := CopyHelperSteps.storage_live options limits remaining span frames frame machine ⟨0,0⟩ 4 2
    sourceBody location (by decide +kernel) (by decide +kernel) RootCompilerFacts.root_storage_trivial_type2 valid4 dead4 noClocks
  have secondStep := CopyHelperSteps.storage_live options limits remaining span frames first machine ⟨0,1⟩ 5 0
    sourceBody rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) valid5First
    (by simpa [first,SourceSteps.liveFrame,Array.getElem_set] using dead5) noClocks
  have allFirst : CopyHelperCleanup.AllImmediate first :=
    CopyHelperCleanup.all_immediate_set frame 4 _ valid4 allImmediate (by intro memory;simp)
  have allDone : CopyHelperCleanup.AllImmediate done :=
    CopyHelperCleanup.all_immediate_set first 5 _ valid5First allFirst (by intro memory;simp)
  refine ⟨first,done,firstStep,secondStep,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,rfl,?_,?_,?_,allDone⟩
  · simp [done,first,SourceSteps.liveFrame]
  · simp [done,first,SourceSteps.liveFrame,Array.getElem?_set]
  · simp [done,first,SourceSteps.liveFrame,Array.getElem?_set,valid4]
  · simp [done,first,SourceSteps.liveFrame,Array.getElem?_set,valid5]

#print axioms actual_two_live
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``actual_two_live) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved axiom {dependency}"
end DuplicatePrefix.CopyHelperEntryBody
