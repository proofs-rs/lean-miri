import Miri.Frontend.FoundationSourceMaterial
open Lean Miri Miri.Input Miri.Frontend.Foundation
private def checked (r : Except String α) : IO α := match r with
| .ok v => pure v | .error e => throw (IO.userError e)
private def rejects (r : Except String α) : IO Unit := match r with
| .error _ => pure () | .ok _ => throw (IO.userError "malformed reify source accepted")
private def replace (j : Json) (key : String) (value : Json) : Except String Json := do
  return Json.mkObj (((← j.getObj?).toArray.toList.filter (·.1 != key)) ++ [(key,value)])
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected genuine function-pointer source")
  let d ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
  let physical ← checked (SourceTypesParser.material d.source)
  let mir ← checked (SourceMirParser.material d (some physical))
  let mut safe := 0
  let mut unsafeCount := 0
  let mut explicit := 0
  let mut generic := 0
  for body in mir.bodies do
    for block in body.blocks do
      for statement in block.statements do
        if let .assign _ (.pointerCoercion (.known (.ReifyFnPointer safety)) (.constant value) target source) := statement.kind then
          let some (.functionPointer signature) := physical.types[target]? | throw (IO.userError "target function pointer source lost")
          unless signature.safety == safety do throw (IO.userError "reify safety changed")
          let some (.functionDefinition _ arguments) := physical.types[value.type]? | throw (IO.userError "source function-item identity lost")
          if !arguments.isEmpty then generic := generic+1
          if safety == .Safe then safe := safe+1 else unsafeCount := unsafeCount+1
          if let .known .AsCast := source then explicit := explicit+1
  unless safe > 0 && unsafeCount > 0 && explicit > 0 && generic > 0 do
    throw (IO.userError "genuine safe/unsafe/explicit/generic coercions absent")
  let mut controls := 0
  for body in d.bodies do
    let blocks ← checked (body.getObjValAs? (Array Json) "blocks")
    for (block,bi) in blocks.zipIdx do
      let statements ← checked (block.getObjValAs? (Array Json) "statements")
      for (statement,si) in statements.zipIdx do
        if (← checked (statement.getObjValAs? String "kind")) != "assign" then continue
        let value ← checked (statement.getObjVal? "value")
        if (← checked (value.getObjValAs? String "kind")) != "pointer_coercion" then continue
        let invalid ← checked (replace statement "value" (← checked (replace value "target" (toJson d.types.size))))
        let altered ← checked (replace block "statements" (toJson (statements.mapIdx fun i row => if i == si then invalid else row)))
        rejects (SourceMirParser.body d (← checked (replace body "blocks" (toJson (blocks.mapIdx fun i row => if i == bi then altered else row)))) none (some physical))
        controls := controls+1
  unless controls > 0 do throw (IO.userError "reify boundary control absent")
  IO.println s!"PASS safe{safe}/unsafe{unsafeCount}/explicit{explicit}/generic{generic} reify syntax; exact fn-item args, safety, source and malformed target controls"
