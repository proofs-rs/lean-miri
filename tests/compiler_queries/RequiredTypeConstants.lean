import Miri.Input.Decoder
import Miri.Input.CompilerLifecycle

open Miri.Input Miri.Interpreter Miri.Memory

private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

private def access : RuntimeArrayQueries.Access (MachineHooks.State Unit RuntimeArrayTypes.World) := {
  get := fun state => state.machine.user
  set := fun state world => {state with machine := {state.machine with user := world}} }

private def sameFrame (left right : Frame Provenance LocalLayout MachineHooks.FrameExtra) : Bool :=
  left.body == right.body && left.bodyIdentity == right.bodyIdentity &&
  left.functionInstance == right.functionInstance && left.returnContinuation == right.returnContinuation &&
  left.returnPlace == right.returnPlace && left.localsIdentity == right.localsIdentity &&
  left.locals == right.locals && left.vaList == right.vaList && left.trackCallerArg == right.trackCallerArg &&
  left.location == right.location && left.extra.userRelevance == right.extra.userRelevance &&
  left.extra.borrowTracker.isNone && right.extra.borrowTracker.isNone &&
  left.extra.catchUnwind.isNone && right.extra.catchUnwind.isNone &&
  left.extra.dataRace.isNone && right.extra.dataRace.isNone

private def sameStack (left right : Stack Provenance LocalLayout MachineHooks.FrameExtra) : Bool :=
  left.frames.size == right.frames.size && (left.frames.zip right.frames).all (fun (a,b) => sameFrame a b)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected genuine raw-type-constant export")
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let program ← must (lowerProgram document)
  let runtime ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let world ← must ((RuntimeArrayTypes.create runtime).mapError reprStr)
  let some source := document.instances.find? (·.defPath == some "const_usize")
    | throw (IO.userError "genuine const_usize instance is absent")
  let some bodyId := source.bodyId | throw (IO.userError "genuine helper body is absent")
  let some (.material body) := document.bodies[bodyId]?
    | throw (IO.userError "genuine helper body is not material")
  let #[good] := body.requiredConsts
    | throw (IO.userError "genuine helper does not have one source required constant")
  let .Ty ty _ := good.value | throw (IO.userError "required Const::Ty was eagerly evaluated")
  let (unresolved,arena) ← must ((TypeArena.World.internConstant
    (.Param 0 "N" (some ty))).run world.arena)
  let world := {world with arena}
  let identity := BodyIdentity.ofCanonicalIndex bodyId
  let (actual,world) ← must ((program.resolveBodyIdentity identity).run world)
  let loaded : LoadedBody := ⟨identity,actual.body⟩
  let (layout,world) ← must ((RuntimeArrayTypes.lookup world ty).mapError reprStr)
  let token := LocalsIdentity.ofAllocationToken 0
  let frame : Frame Provenance LocalLayout MachineHooks.FrameExtra :=
    Frame.create loaded source.id ⟨none,none,0,none⟩ (.stop false)
      (.frameLocal 0 0 none layout token) good.span token
  let state : MachineHooks.State Unit RuntimeArrayTypes.World := {
    stack := ⟨#[frame]⟩
    machine := {
      memory := MemoryState.empty
      borrowTracker := none
      dataRace := none
      threads := Miri.Concurrency.ThreadManager.initial false
      raceAllocations := #[]
      allocationSpans := #[]
      user := world} }
  let prepared := CompilerLifecycle.prepare program
  match CompilerLifecycle.requiredConstants prepared access loaded state with
  | .ok () after =>
    unless after.machine.memory.nextAllocId == state.machine.memory.nextAllocId &&
        sameStack after.stack state.stack do
      throw (IO.userError "required scalar conversion changed memory or entered the first instruction")
  | .error error _ => throw (IO.userError s!"genuine required raw constant failed: {reprStr error}")
  let changed := {body with requiredConsts := #[{good with value := .Ty ty unresolved}]}
  let source := {document with bodies := document.bodies.setIfInBounds bodyId (.material changed)}
  let changedWorld := {world with metadata := {world.metadata with source, checkedMaterial := none, denseTypes := none}}
  let changedState := {state with machine := {state.machine with user := changedWorld}}
  match CompilerLifecycle.requiredConstants prepared access loaded changedState with
  | .error (.unsupported reason) after =>
    unless reason.contains "tooGeneric" && sameStack after.stack changedState.stack &&
        after.machine.memory.nextAllocId == changedState.machine.memory.nextAllocId do
      throw (IO.userError "required-constant failure lost its typed cause, frame or event order")
  | .ok _ _ => throw (IO.userError "unused required constant was skipped")
  | .error error _ => throw (IO.userError s!"required constant failed for the wrong reason: {reprStr error}")
  IO.println "PASS genuine required Const::Ty evaluation and unused TooGeneric failure before body execution"
