import Miri.Input.Decoder
import Miri.Input.DefinitionPathHash

open Lean Miri.Input
private def must (value : Except String A) : IO A :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def decimal (value : Json) (key : String) : IO Nat := do
  let text ← must ((← must (value.getObjVal? key)).getStr?)
  let some value := text.toNat? | throw (IO.userError "invalid oracle decimal")
  pure value
private def replaceField (value : Json) (key : String) (replacement : Json) : Except String Json := do
  let fields ← value.getObj?
  let _ ← value.getObjVal? key
  pure (Json.mkObj (fields.toList.map fun (name,value) =>
    (name,if name == key then replacement else value)))
def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath] := args | throw (IO.userError "expected fresh producer and raw DefKey oracle")
  let source := (← must (decodeJson (← IO.FS.readFile sourcePath))).document
  let oracle ← must ((← must (Json.parse (← IO.FS.readFile oraclePath))).getArr?)
  let mut count := 0
  let mut lifetimes := 0
  for row in oracle do
    let crateIndex ← must ((← must (row.getObjVal? "crate")).getNat?)
    let index ← must ((← must (row.getObjVal? "index")).getNat?)
    let some definition := source.definitions.find? (fun value =>
      value.crateIndex == crateIndex && value.index == index) | continue
    let some path := definition.rawPath | throw (IO.userError "demanded definition lacks raw DefKey material")
    let actual ← must (DefinitionPathHash.query path)
    unless actual.toNat == (← decimal row "hash") do
      throw (IO.userError "raw DefKey hash differs from pinned compiler")
    unless path.stableCrateId.toNat == (← decimal row "stable_crate") do
      throw (IO.userError "raw stable crate identity changed")
    if path.components.any (fun component => component.kind == "lifetime") then
      unless path.genericHeader.isNone do throw (IO.userError "lifetime definition acquired a generic header")
      lifetimes := lifetimes + 1
    let broken := {path with components := #[]}
    if (DefinitionPathHash.query broken).isOk then throw (IO.userError "missing DefKey root accepted")
    let bad := {path with components := path.components.push ⟨"type",none,0⟩}
    if (DefinitionPathHash.query bad).isOk then throw (IO.userError "missing DefKey symbol accepted")
    let bad := {path with components := path.components.push ⟨"unsupported",none,0⟩}
    if (DefinitionPathHash.query bad).isOk then throw (IO.userError "unknown DefKey family accepted")
    let bad := {path with components := path.components.push ⟨"closure",none,2^32⟩}
    if (DefinitionPathHash.query bad).isOk then throw (IO.userError "out-of-range DefKey disambiguator accepted")
    count := count + 1
  unless count >= 15 && lifetimes > 0 do throw (IO.userError "insufficient raw definition/lifetime oracle coverage")
  let raw ← must (Json.parse (← IO.FS.readFile sourcePath))
  let definitions ← must ((← must (raw.getObjVal? "definitions")).getArr?)
  let some first := definitions[0]? | throw (IO.userError "raw definition mutation control absent")
  let path ← must (first.getObjVal? "raw_path")
  let stable ← must ((← must (path.getObjVal? "stable_crate_id")).getNat?)
  let badPath ← must (replaceField path "stable_crate_id" (toJson ((stable + 1) % 2^64)))
  let badFirst ← must (replaceField first "raw_path" badPath)
  let bad ← must (replaceField raw "definitions" (toJson (#[badFirst] ++ definitions.extract 1 definitions.size)))
  match decodeJson bad.compress with
  | .ok _ => throw (IO.userError "conflicting physical/stable crate identity accepted")
  | .error error =>
    unless error.contains "physical crate has conflicting stable crate identities" do
      throw (IO.userError s!"physical/stable identity control failed for another reason: {error}")
  let crates ← definitions.mapM fun definition => do
    must ((← must (definition.getObjVal? "crate")).getNat?)
  let freshCrate := (crates.foldl max 0) + 1
  let badFirst ← must (replaceField first "crate" (toJson freshCrate))
  let bad ← must (replaceField raw "definitions" (toJson (#[badFirst] ++ definitions.extract 1 definitions.size)))
  match decodeJson bad.compress with
  | .ok _ => throw (IO.userError "one stable crate identity accepted for two physical crates")
  | .error error =>
    unless error.contains "stable crate identity belongs to multiple physical crates" do
      throw (IO.userError s!"stable/physical identity control failed for another reason: {error}")
  let mut checkedDefault := false
  for (definition,index) in definitions.zipIdx do
    let path ← must (definition.getObjVal? "raw_path")
    let header ← must (path.getObjVal? "generic_header")
    if header == .null then continue
    let defaults ← must ((← must (header.getObjVal? "default_expressions")).getArr?)
    if !defaults.any (· != .null) then continue
    let invalid := Json.mkObj [("kind",toJson "node"),("sort",toJson "type"),
      ("tag",toJson "imaginary"),("payload",toJson ""),("children",toJson (#[] : Array Json))]
    let defaults := defaults.map fun value => if value == .null then value else invalid
    let header ← must (replaceField header "default_expressions" (toJson defaults))
    let path ← must (replaceField path "generic_header" header)
    let definition ← must (replaceField definition "raw_path" path)
    let changed := definitions.mapIdx fun i value => if i == index then definition else value
    let bad ← must (replaceField raw "definitions" (toJson changed))
    if (decodeJson bad.compress).isOk then throw (IO.userError "closed unknown raw generic default accepted")
    checkedDefault := true
    break
  unless checkedDefault do throw (IO.userError "missing raw generic default corruption control")
  IO.println s!"PASS {count} compiler DefPathHash reconstructions with {lifetimes} raw lifetime definitions and malformed controls"
