import empty_function.InitializationPrefix

/-! Internal composition of actual memory-call initialization outcomes.
Protection totality is a remaining semantic obligation, not caller validity. -/
namespace EmptyFunction.MemoryInitOutcome
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

abbrev Machine := MachineHooks.MachineState MiriMemoryKind Configuration.RootUser

/-- Protection may replace its frame borrow state and machine, while retaining
all ordinary frame fields, including caller destination and continuation. -/
def SameFrameExceptBorrow (before after : LocalUnit.F) : Prop :=
  after = {before with extra := {before.extra with borrowTracker := after.extra.borrowTracker}}

def readyFrame (frame : LocalUnit.F) : LocalUnit.F :=
  {frame with locals := #[{value := .live (.immediate .uninit),layout := none}], location := .mir .start}

theorem tail_error (s : Static) (place : MPlaceTy Provenance) (span : SpanRef)
    (before failed : State) (error : StepError)
    (protection : (ExecutionMachine.callHooks s.cfg s.limits).protectArgument () place before =
      .error error failed) :
    InitializationPrefix.protectedTail s place span before = .error error failed := by
  simp [InitializationPrefix.protectedTail,protection,bind,Bind.bind,EStateM.bind]

theorem tail_ok (s : Static) (metadata : Metadata s) (place : MPlaceTy Provenance)
    (span : SpanRef) (before : State) (frames : Array LocalUnit.F) (frame : LocalUnit.F)
    (machine : Machine)
    (protection : (ExecutionMachine.callHooks s.cfg s.limits).protectArgument () place before =
      .ok () (LocalUnit.current frames frame machine))
    (body : Meaning.FrameMatches frame s.loaded)
    (locals : frame.locals = #[{value := .dead,layout := none}])
    (noClocks : frame.extra.dataRace = none) :
    InitializationPrefix.protectedTail s place span before =
      .ok () (LocalUnit.current frames (readyFrame frame) machine) := by
  unfold InitializationPrefix.protectedTail
  simp only [bind,Bind.bind,EStateM.bind,protection]
  rw [CanonicalInit.span_current]
  dsimp only
  rw [CanonicalInit.push_done s metadata (InitializationPrefix.capacity_positive s)
    frames {frame with location := .unwinding span} machine body locals noClocks]
  rfl

/-- The source-derived pre-protection certificate; no stage outcome has been
assumed. Its existence follows from ordinary metadata/current input. -/
structure Prefix (s : Static) (metadata : Metadata s) (p : Packet)
    (input : InputDraft.CurrentInputDraft s p)
    (destination : InputDraft.MemoryDestination s p input.tracker) where
  frame : LocalUnit.F
  machine : Machine
  actual : install s p = InitializationPrefix.protectedTail s destination.place metadata.preamble
    (LocalUnit.current p.before.stack.frames {frame with location := .unwinding metadata.localSpan} machine)
  body : Meaning.FrameMatches frame s.loaded
  identity : frame.bodyIdentity = s.loaded.identity
  function : frame.functionInstance = s.functionInstance
  location : frame.location = .unwinding metadata.preamble
  locals : frame.locals = #[{value := .dead,layout := none}]
  borrowed : frame.extra.borrowTracker = some {}
  noClocks : frame.extra.dataRace = none
  returnPlace : frame.returnPlace = p.destination
  continuation : frame.returnContinuation =
    CanonicalInit.normalizedContinuation s (.goto (some p.returnBlock) p.unwind)
  varargs : frame.vaList = #[]
  callerArg : frame.trackCallerArg = none
  machineTracker : machine.borrowTracker = some input.tracker
  noRace : machine.dataRace = none
  noGhost : machine.user.payload.ghost = false
  shallow : machine.user.payload.validation = .Shallow
  pushed : ∃ previous, machine = FrameRelevance.pushedMachine p.before.stack.frames frame previous
    (s.cfg.lifecycle.freshLocalsIdentity p.before.machine).1

theorem from_current (s : Static) (metadata : Metadata s) (profile : Profile s) (p : Packet)
    (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (destination : InputDraft.MemoryDestination s p input.tracker) :
    Nonempty (Prefix s metadata p input destination) := by
  obtain ⟨frame,machine,actual,body,identity,function,location,locals,borrowed,noClocks,
    returnPlace,continuation,varargs,callerArg,machineTracker,noRace,noGhost,shallow,pushed⟩ :=
    InitializationPrefix.memory_prefix s metadata profile p runtime input destination
  exact ⟨⟨frame,machine,actual,body,identity,function,location,locals,borrowed,noClocks,
    returnPlace,continuation,varargs,callerArg,machineTracker,noRace,noGhost,shallow,pushed⟩⟩

/-- Internal disjunction to be proved from the source protection operation.
Failure states and errors are exact; success carries arbitrary semantic facts. -/
def ProtectionOutcome (s : Static) (place : MPlaceTy Provenance) (frames : Array LocalUnit.F)
    (frame : LocalUnit.F) (machine : Machine) (Post : LocalUnit.F → Machine → Prop) : Prop :=
  (∃ error failed,
    (ExecutionMachine.callHooks s.cfg s.limits).protectArgument () place
      (LocalUnit.current frames frame machine) = .error error failed ∧
    RunLoop.reportsUB error = false) ∨
  (∃ changedFrame changed,
    (ExecutionMachine.callHooks s.cfg s.limits).protectArgument () place
      (LocalUnit.current frames frame machine) = .ok () (LocalUnit.current frames changedFrame changed) ∧
    SameFrameExceptBorrow frame changedFrame ∧ Post changedFrame changed)

/-- Actual initialization either stops with the exact non-UB error/state or
enters MIR00 with the original ordinary frame fields and all supplied posts.
The protection argument is an internal semantic obligation, not public input. -/
theorem memory_outcome (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (destination : InputDraft.MemoryDestination s p input.tracker)
    (Post : LocalUnit.F → Machine → Prop)
    (protection : ∀ entry : Prefix s metadata p input destination,
      ProtectionOutcome s destination.place p.before.stack.frames
        {entry.frame with location := .unwinding metadata.localSpan} entry.machine Post) :
    (∃ error failed, install s p = .error error failed ∧ RunLoop.reportsUB error = false) ∨
    (∃ entry : Prefix s metadata p input destination,
      ∃ changedFrame changed,
        SameFrameExceptBorrow {entry.frame with location := .unwinding metadata.localSpan} changedFrame ∧
        Post changedFrame changed ∧
        install s p = .ok () (LocalUnit.current p.before.stack.frames (readyFrame changedFrame) changed) ∧
        (LocalUnit.current p.before.stack.frames (readyFrame changedFrame) changed).stack.frames.size = depth p ∧
        Meaning.FrameMatches changedFrame s.loaded ∧ changedFrame.bodyIdentity = s.loaded.identity ∧
        changedFrame.functionInstance = s.functionInstance ∧
        changedFrame.locals = #[{value := .dead,layout := none}] ∧ changedFrame.extra.dataRace = none) := by
  obtain ⟨entry⟩ := from_current s metadata profile p runtime input destination
  rcases protection entry with failed | succeeded
  · obtain ⟨error,failed,actual,nonUB⟩ := failed
    left
    exact ⟨error,failed,entry.actual.trans
      (tail_error s destination.place metadata.preamble _ failed error actual),nonUB⟩
  · obtain ⟨changedFrame,changed,actual,same,post⟩ := succeeded
    have body : Meaning.FrameMatches changedFrame s.loaded := by rw [same];exact entry.body
    have identity : changedFrame.bodyIdentity = s.loaded.identity := by rw [same];exact entry.identity
    have function : changedFrame.functionInstance = s.functionInstance := by rw [same];exact entry.function
    have locals : changedFrame.locals = #[{value := .dead,layout := none}] := by rw [same];exact entry.locals
    have noClocks : changedFrame.extra.dataRace = none := by rw [same];exact entry.noClocks
    right
    refine ⟨entry,changedFrame,changed,same,post,?_,?_,body,identity,function,locals,noClocks⟩
    · exact entry.actual.trans (tail_ok s metadata destination.place metadata.preamble _
        p.before.stack.frames changedFrame changed actual body locals noClocks)
    · simp [LocalUnit.current,depth]

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.MemoryInitOutcome.").length != 1 then
      count := count+1
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved memory-init outcome axiom {dependency} in {name}"
  logInfo m!"Audited {count} memory-init outcome declarations"
end EmptyFunction.MemoryInitOutcome
