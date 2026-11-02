import duplicate_prefix.CopyScopedInstall
import duplicate_prefix.CopyFinish
import duplicate_prefix.CopyArgumentProperties
namespace DuplicatePrefix.CopyTail
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts CopyFrameData
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable def trackedRoot (root : RootFrame) (callerSpan : SpanRef) : RootFrame :=
  {root with frame := {root.frame with trackCallerArg := some callerSpan}}
noncomputable def action (h : CopyCallCore.RootHooks) (callerSpan : SpanRef)
    (source targetPointer : Scalar Provenance) (n : UInt64) (destinationOp : OpTy Provenance) :
    MachineHooks.M MiriMemoryKind Machine.RootUser Unit := do
  let destinationMplace := match destinationOp.op with
    | .indirect place => some (MPlaceTy.mk place destinationOp.layout)
    | .immediate _ => none
  let frame ← h.getFrame
  let preamble ← match frame.location with
    | .unwinding span => pure span
    | .mir _ => throw (.invalidProgram "raw frame does not have preamble location")
  h.setFrame {frame with trackCallerArg := some callerSpan}
  let (callerIndex,calleeIndex) ← h.withRetagMode () .FnEntry
    (CopyCallCore.argumentBody h (CopyInstall.first source) (CopyInstall.second targetPointer) (CopyInstall.third n))
  CopyCallCore.spanAt h (← h.localSpan HelperCompilerFacts.copyBody.body 0)
  unless ← h.checkArgumentCompat () HelperCompilerFacts.copyAbi.ret HelperCompilerFacts.copyAbi.ret do
    throw (.undefinedBehavior "AbiMismatchReturn")
  if let some mplace := destinationMplace then h.protectArgument () mplace
  CopyCallCore.spanAt h preamble
  let _ ← CopyCallCore.implicitAbi calleeIndex
  CopyCallCore.require (calleeIndex+1 == HelperCompilerFacts.copyAbi.args.size) "mismatch between callee ABI and callee body arguments"
  if callerIndex < 3 then throw (.undefinedBehavior "calling a function with more arguments than it expected")
  h.afterFrameInit ()
  h.pushDone ()
 theorem core_eq (h : CopyCallCore.RootHooks) (source targetPointer : Scalar Provenance) (n : UInt64)
    (destination : RuntimeStackPlace Provenance) (cont : ReturnContinuation) :
    CopyCallCore.core h (CopyInstall.first source) (CopyInstall.second targetPointer) (CopyInstall.third n) destination cont = (do
      let callerSpan ← h.callerLocation
      let destinationOp ← h.placeToOp () destination
      h.pushRaw () HelperCompilerFacts.copyCall.callee HelperCompilerFacts.copyBody destination cont
      action h callerSpan source targetPointer n destinationOp) := by
  unfold CopyCallCore.core action
  simp only [bind_assoc]
  rfl
 theorem run (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra)) (root : RootFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (source targetPointer : Scalar Provenance) (n : UInt64) (old : Immediate Provenance) (destLayout : LocalLayout)
    (preamble callerSpan : SpanRef) (located : root.frame.location = .unwinding preamble)
    (dead0 : (root.frame.locals[0]'(root.valid ⟨0,by decide⟩)).value = .dead)
    (dead : ∀ index : Fin 3, (root.frame.locals[index.val+1]'(root.valid (CopyInstall.argId index))).value = .dead)
    (uncached : ∀ index : Fin 3, (root.frame.locals[index.val+1]'(root.valid (CopyInstall.argId index))).layout = none)
    (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow) :
    action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      callerSpan source targetPointer n ⟨.immediate old,destLayout⟩ (Storage.withCurrent frames root.frame machine) =
      .ok () (Storage.withCurrent frames
        (CopyDone.doneFrame {(CopyInstall.result (trackedRoot root callerSpan) source targetPointer n).frame with location := .unwinding preamble}) machine) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  let selected := trackedRoot root callerSpan
  let after := CopyInstall.result selected source targetPointer n
  have getFrame := CallEntryLocals.get_frame options limits (remaining+1) span frames root.frame machine
  have setFrame := CallEntryLocals.set_frame options limits (remaining+1) span frames root.frame selected.frame machine
  have install := CopyScopedInstall.install options limits remaining span debug fuel validationFuel frames selected machine
    tracker tracked source targetPointer n dead uncached ghost shallow
  have afterDead : (after.frame.locals[0]'(after.valid ⟨0,by decide⟩)).value = .dead := by
    rw [CopyArgumentProperties.untouched selected source targetPointer n ⟨0,by decide⟩ (by decide) (by decide) (by decide)]
    exact dead0
  have finish := CopyFinish.finish options limits (remaining+1) span frames after.frame machine preamble
    after.body after.identity after.callee (after.valid ⟨0,by decide⟩) afterDead after.noClocks
  unfold action
  simp only [bind,EStateM.bind]
  rw [getFrame]
  simp only [located, pure, EStateM.pure, EStateM.bind]
  dsimp only [selected,trackedRoot] at setFrame
  simp only [located] at setFrame
  rw [setFrame]
  simp only [EStateM.bind]
  dsimp only [selected,trackedRoot] at install
  simp only [located] at install
  rw [install]
  simp only [EStateM.bind]
  exact finish
end DuplicatePrefix.CopyTail
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.CopyTail.core_eq, ``DuplicatePrefix.CopyTail.run] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved add tail dependency {dependency}"
