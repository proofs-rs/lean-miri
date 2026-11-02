import duplicate_prefix.MetadataLocalStages
import duplicate_prefix.MetadataArgument
import duplicate_prefix.MetadataCallCore
namespace DuplicatePrefix.MetadataInstall
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
open CanonicalConfigFacts
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def spanFrame (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) :=
  {frame with location := .unwinding ⟨635⟩}
def cacheFrame (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (valid : 1 < frame.locals.size) :=
  LocalOperands.cachedLayoutFrame (spanFrame frame) 1 PtrMetadataHelper.rawLayout valid

def resultFrame (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (valid : 1 < frame.locals.size)
    (value : Immediate Provenance) :=
  let cached := cacheFrame frame valid
  let live := RootArgumentEntry.liveFrame cached 1 (by simpa [cached,cacheFrame, spanFrame,LocalOperands.cachedLayoutFrame] using valid)
  {live with locals := (live.locals.set 1 {value := .live (.immediate value),layout := some PtrMetadataHelper.rawLayout}
    (by simpa [live,cached,RootArgumentEntry.liveFrame,cacheFrame,spanFrame,LocalOperands.cachedLayoutFrame] using valid))}

def action (h : RootCallCore.RootHooks) (value : Immediate Provenance) : MachineHooks.M MiriMemoryKind Machine.RootUser (Nat × Nat) := do
  MetadataCallCore.spanAt h (← h.localSpan PtrMetadataHelper.body.body 1)
  let ty ← h.localLayout () 1
  Call.passArgument h () (.Copy ⟨.immediate value,PtrMetadataHelper.rawLayout⟩)
    (PtrMetadataHelper.abi.args.getD 0 PtrMetadataHelper.abi.ret)
    (PtrMetadataHelper.abi.args.getD 0 PtrMetadataHelper.abi.ret) 0 ⟨1,#[]⟩ ty.ty false
  pure (1,1)

theorem install (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (carrier : Pointer Provenance ⊕ UInt64) (len : UInt64)
    (valid : 1 < frame.locals.size)
    (body : frame.body = PtrMetadataHelper.body.body)
    (identity : frame.bodyIdentity = PtrMetadataHelper.body.identity)
    (callee : frame.functionInstance = PtrMetadataHelper.resolved.callee)
    (uncached : frame.locals[1].layout = none) (dead : frame.locals[1].value = .dead)
    (noClocks : frame.extra.dataRace = none) (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow) :
    action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      (PtrMetadataComplete.rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len)
      (Storage.withCurrent frames frame machine) =
      .ok (1,1) (Storage.withCurrent frames
        (resultFrame frame valid (PtrMetadataComplete.rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len)) machine) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  have query := MetadataLocalStages.span1 options limits (remaining+1) span frames frame machine body identity callee
  have setspan := CallEntryLocals.set_span options limits (remaining+1) span frames frame machine ⟨635⟩
  change MetadataCallCore.spanAt h ⟨635⟩ (Storage.withCurrent frames frame machine) = _ at setspan
  have layout := MetadataLocalStages.layout1 options limits (remaining+1) span frames (spanFrame frame) machine
    body identity callee valid uncached
  have cachedValid : 1 < (cacheFrame frame valid).locals.size := by simpa [cacheFrame,spanFrame,LocalOperands.cachedLayoutFrame] using valid
  have cached : (cacheFrame frame valid).locals[1].layout = some PtrMetadataHelper.rawLayout := by
    simp [cacheFrame,LocalOperands.cachedLayoutFrame,Array.getElem_set_self]
  have deadCached : (cacheFrame frame valid).locals[1].value = .dead := by
    simpa [cacheFrame,LocalOperands.cachedLayoutFrame,Array.getElem_set_self,spanFrame] using dead
  have passed := MetadataArgument.pass_argument options limits remaining span debug frames (cacheFrame frame valid)
    machine carrier len cachedValid body cached deadCached noClocks fuel validationFuel ghost shallow
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
  rw [PtrMetadataHelper.raw_layout_type]
  rw [passed]
  simp only [pure,Pure.pure,EStateM.pure]
  congr 1
  simp [resultFrame,cacheFrame,spanFrame,LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame,Array.getElem_set_self]
end
end DuplicatePrefix.MetadataInstall
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.MetadataInstall.install) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved metadata installation dependency {dependency}"
