import duplicate_prefix.LenLocalStages
import duplicate_prefix.LenArgument
import duplicate_prefix.LenCallCore
namespace DuplicatePrefix.LenInstall
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
open CanonicalConfigFacts
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def spanFrame (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) :=
  {frame with location := .unwinding ⟨LenSpans.span1⟩}
def cacheFrame (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (valid : 1 < frame.locals.size) :=
  LocalOperands.cachedLayoutFrame (spanFrame frame) 1 LenHelper.rawLayout valid

def resultFrame (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (valid : 1 < frame.locals.size)
    (value : Immediate Provenance) :=
  let cached := cacheFrame frame valid
  let live := RootArgumentEntry.liveFrame cached 1 (by simpa [cached,cacheFrame, spanFrame,LocalOperands.cachedLayoutFrame] using valid)
  {live with locals := (live.locals.set 1 {value := .live (.immediate value),layout := some LenHelper.rawLayout}
    (by simpa [live,cached,RootArgumentEntry.liveFrame,cacheFrame,spanFrame,LocalOperands.cachedLayoutFrame] using valid))}

def action (h : RootCallCore.RootHooks) (value : Immediate Provenance) : MachineHooks.M MiriMemoryKind Machine.RootUser (Nat × Nat) := do
  LenCallCore.spanAt h (← h.localSpan LenHelper.body.body 1)
  let ty ← h.localLayout () 1
  Call.passArgument h () (.Copy ⟨.immediate value,LenHelper.rawLayout⟩)
    (LenHelper.abi.args.getD 0 LenHelper.abi.ret)
    (LenHelper.abi.args.getD 0 LenHelper.abi.ret) 0 ⟨1,#[]⟩ ty.ty false
  pure (1,1)

theorem install_of_copy (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (value : Immediate Provenance)
    (valid : 1 < frame.locals.size)
    (body : frame.body = LenHelper.body.body)
    (identity : frame.bodyIdentity = LenHelper.body.identity)
    (callee : frame.functionInstance = LenHelper.resolved.callee)
    (uncached : frame.locals[1].layout = none) (dead : frame.locals[1].value = .dead)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (after : CanonicalConfigFacts.RootState)
    (copy : (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate value,LenHelper.rawLayout⟩
      (LocalPlaces.localRuntimePlace frames.size (RootArgumentEntry.liveFrame (cacheFrame frame valid) 1
        (by simpa [cacheFrame,spanFrame,LocalOperands.cachedLayoutFrame] using valid)) 1 LenHelper.rawLayout).stackView
      (Storage.withCurrent frames (RootArgumentEntry.liveFrame (cacheFrame frame valid) 1
        (by simpa [cacheFrame,spanFrame,LocalOperands.cachedLayoutFrame] using valid)) machine) = .ok () after) :
    action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      value
      (Storage.withCurrent frames frame machine) =
      .ok (1,1) after := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  have query := LenLocalStages.span1 options limits (remaining+1) span frames frame machine body identity callee
  have setspan := CallEntryLocals.set_span options limits (remaining+1) span frames frame machine ⟨LenSpans.span1⟩
  change LenCallCore.spanAt h ⟨LenSpans.span1⟩ (Storage.withCurrent frames frame machine) = _ at setspan
  have layout := LenLocalStages.layout1 options limits (remaining+1) span frames (spanFrame frame) machine
    body identity callee valid uncached
  have cachedValid : 1 < (cacheFrame frame valid).locals.size := by simpa [cacheFrame,spanFrame,LocalOperands.cachedLayoutFrame] using valid
  have cached : (cacheFrame frame valid).locals[1].layout = some LenHelper.rawLayout := by
    simp [cacheFrame,LocalOperands.cachedLayoutFrame,Array.getElem_set_self]
  have deadCached : (cacheFrame frame valid).locals[1].value = .dead := by
    simpa [cacheFrame,LocalOperands.cachedLayoutFrame,Array.getElem_set_self,spanFrame] using dead
  have passed := LenArgument.pass_argument_of_copy options limits remaining span debug frames (cacheFrame frame valid)
    machine value cachedValid body cached deadCached noClocks ghost after copy
  dsimp only [spanFrame] at layout
  dsimp only [cacheFrame,spanFrame] at passed
  unfold action
  simp only [bind,EStateM.bind]
  rw [query]
  dsimp only
  rw [setspan]
  dsimp only
  rw [layout]
  dsimp only
  rw [LenHelper.raw_layout_type]
  rw [passed]
  rfl

end
end DuplicatePrefix.LenInstall
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.LenInstall.install_of_copy) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved metadata installation dependency {dependency}"
