import Miri.Frontend.FoundationSourceMaterial
open Lean Miri Miri.Input Miri.Frontend.Foundation
private def checked (r : Except String α) : IO α := match r with
| .ok value => pure value | .error e => throw (IO.userError e)
private def rejects (r : Except String α) : IO Unit := match r with
| .error _ => pure () | .ok _ => throw (IO.userError "malformed union aggregate accepted")
private def replace (j : Json) (key : String) (value : Json) : Except String Json := do
  return Json.mkObj (((← j.getObj?).toArray.toList.filter (·.1 != key)) ++ [(key,value)])
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected genuine union source")
  let d ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
  let physical ← checked (SourceTypesParser.material d.source)
  let mir ← checked (SourceMirParser.material d (some physical))
  let mut unionFields : Array Nat := #[]
  let mut generic := 0
  let mut structs := 0
  for body in mir.bodies do
    for block in body.blocks do
      for statement in block.statements do
        if let .assign _ (.aggregateAdt definition _ arguments userType active operands) := statement.kind then
          unless userType.isNone do throw (IO.userError "unexpected source annotation")
          let some declared := physical.definitions[definition]? | throw (IO.userError "ADT declaration absent")
          let some adt := declared.adt | throw (IO.userError "nonADT aggregate")
          match adt.kind with
          | .unionKind =>
            let some field := active | throw (IO.userError "union active field lost")
            unless operands.size == 1 do throw (IO.userError "union operand lost")
            unionFields := unionFields.push field
            if !arguments.isEmpty then generic := generic+1
          | .structKind => structs := structs+1
          | _ => pure ()
  unless unionFields.contains 0 && unionFields.contains 1 && generic > 0 && structs > 0 do
    throw (IO.userError "actual union fields/generic args/struct source coverage absent")
  let mut controls := 0
  for body in d.bodies do
    let blocks ← checked (body.getObjValAs? (Array Json) "blocks")
    for (block,bi) in blocks.zipIdx do
      let statements ← checked (block.getObjValAs? (Array Json) "statements")
      for (statement,si) in statements.zipIdx do
        if (← checked (statement.getObjValAs? String "kind")) != "assign" then continue
        let value ← checked (statement.getObjVal? "value")
        if (← checked (value.getObjValAs? String "kind")) != "aggregate_adt" then continue
        let active ← checked (value.getObjValAs? (Option Nat) "active_field")
        if active.isNone then continue
        for (key,altered) in #[("active_field",Json.null),("active_field",toJson (some 999 : Option Nat)),
            ("variant",toJson 999),("definition",toJson d.definitions.size),("operands",toJson (#[] : Array Json))] do
          let newStatement ← checked (replace statement "value" (← checked (replace value key altered)))
          let newStatements := statements.mapIdx fun i row => if i == si then newStatement else row
          let newBlock ← checked (replace block "statements" (toJson newStatements))
          let newBlocks := blocks.mapIdx fun i row => if i == bi then newBlock else row
          let changed ← checked (replace body "blocks" (toJson newBlocks))
          rejects (SourceMirParser.body d changed none (some physical))
        controls := controls+1
  unless controls > 0 do throw (IO.userError "union boundary controls absent")
  IO.println s!"PASS {unionFields.size} union aggregates preserve field0/field1/full generic args; struct source and malformed field/variant/definition/operand controls"
