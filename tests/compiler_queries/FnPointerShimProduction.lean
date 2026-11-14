import Miri.Input.Decoder
import Miri.Input.CallResolution
import Miri.Input.CompilerInstanceAbi

/-! Concrete FnPtr conversion shims carry rustc MIR and FnAbi rows. A newly
constructed shim has neither result and must stop at the exact demand. -/
open Miri.Input

private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

def main (args : List String) : IO Unit := do
  let [path, countText] := args | throw (IO.userError "expected fresh export and shim count")
  let some expectedCount := countText.toNat? | throw (IO.userError "expected numeric shim count")
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let metadata ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let initial ← must ((RuntimeArrayTypes.create metadata).mapError reprStr)
  let program ← must (lowerProgram document)
  let prepared ← must (CallResolution.prepareWithRuntime metadata program)
  let abi ← must (CompilerInstanceAbi.prepare metadata program)
  let mut count := 0
  for (source,id) in document.instances.zipIdx do
    let some (definition,selfType,asPointer) := (match source.instanceKind with
      | .Shim (.FnPtrAsPtr definition selfType) => some (definition,selfType,true)
      | .Shim (.FnPtrFromPtr definition selfType) => some (definition,selfType,false)
      | _ => none)
      | continue
    let some bodyIndex := document.bodies.findIdx? (·.instanceId == id)
      | throw (IO.userError "concrete shim has no rustc body")
    let some seed := document.bodies[bodyIndex]?
      | throw (IO.userError "concrete shim body index disappeared")
    let .material body := seed
      | throw (IO.userError "concrete shim body is not rustc material")
    let (loaded,world) ← must ((CallResolution.loadedBodyOfInstance prepared id).run initial)
    unless loaded.identity.index == bodyIndex && loaded.body == body.mir do
      throw (IO.userError "loaded shim differs from rustc material body")
    let _ ← must ((CompilerInstanceAbi.abiOfInstanceInWorld abi id #[]).run world)
    let novel : RuntimeArrayTypes.CompilerM Unit := do
      let world ← get
      let some node := document.types[selfType]? | throw "FnPtr type absent"
      let constructor ← match world.arena.materialKey node with
        | .ok value => pure value | .error error => throw error
      let some (.functionPointer signature) := constructor | throw "FnPtr constructor absent"
      let ty ← RuntimeArrayTypes.liftType
        (TypeArena.World.internType (.functionPointer {signature with safe := !signature.safe}))
      unless ty >= document.types.size do throw "novel FnPtr reused material type"
      let novelKind := Miri.Interpreter.CallInstanceKind.Shim
        (if asPointer then .FnPtrAsPtr definition ty else .FnPtrFromPtr definition ty)
      let instanceId ← RuntimeArrayTypes.internInstance novelKind #[.Type ty]
      unless instanceId >= document.instances.size do throw "novel shim reused material instance"
      let current ← get
      match (CallResolution.loadedBodyOfInstance prepared instanceId).run current with
      | .error "constructed instance has no exact rustc body result" => pure ()
      | .error error => throw s!"unexpected constructed body error: {error}"
      | .ok _ => throw "constructed shim borrowed rustc body"
    let _ ← must (novel.run world)
    count := count + 1
  unless count == expectedCount do
    throw (IO.userError s!"expected {expectedCount} concrete FnPtr shims, found {count}")
  IO.println s!"PASS {count} rustc material FnPtr shim MIR/ABI rows and constructed rejection"
