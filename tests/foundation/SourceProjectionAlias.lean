import Miri.Frontend.FoundationSourceTypes
open Lean Miri Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def rejects (value : Except String α) : IO Unit :=
  match value with | .ok _ => throw (IO.userError "malformed projection source accepted") | .error _ => pure ()
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected genuine projection header source")
  let source ← checked (Json.parse (← IO.FS.readFile path))
  let material ← checked (SourceTypesParser.material source)
  let mut count := 0
  for id in [:material.types.size] do
    if let some (.projectionAlias definition parent arguments) := material.types[id]? then
      count := count + 1
      unless (material.definitions[definition]?).any (·.kind == "AssocTy") &&
          (material.definitions[parent]?).any (·.kind == "Trait") do
        throw (IO.userError "projection declaration/parent category changed")
      match Input.SourceTypes.instantiate material #[] #[] id with
      | .error "Unsupported source associated type projection normalization" => pure ()
      | _ => throw (IO.userError "projection source was eagerly evaluated or lost")
      if h : id < material.types.size then
        let invalid := material.types.set id (.projectionAlias material.definitions.size parent arguments) h
        rejects ({material with types := invalid}.validate)
        let invalid := material.types.set id (.projectionAlias definition material.definitions.size arguments) h
        rejects ({material with types := invalid}.validate)
        let invalid := material.types.set id (.projectionAlias definition parent #[.type material.types.size]) h
        rejects ({material with types := invalid}.validate)
      else throw (IO.userError "projection index absent")
  unless count > 0 do throw (IO.userError "genuine associated projection source absent")
  IO.println s!"retained {count} genuine projection aliases with exact source references; normalization unavailable and malformed references reject"
