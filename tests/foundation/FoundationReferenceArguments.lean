import Miri.Frontend.FoundationSignatureFnAbi
import Miri.Input.Decoder

open Lean Miri Miri.Frontend.Foundation
private def expect (r : Except String α) : IO α :=
  match r with | .ok a => pure a | .error e => throw (IO.userError e)
private def check (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)
private def rejects (r : Except String α) : IO Unit :=
  match r with | .error _ => pure () | .ok _ => throw (IO.userError "unavailable/unsupported ABI source accepted")

-- Comparison adapter only: table IDs stay local to each compiler document.
private def sameType (r : PhysicalTypeRegistry) (reference : Input.ImportDocument) :
    Nat → Nat → Nat → Except String Bool
  | 0, _, _ => throw "comparison type recursion exhausted"
  | fuel+1, left, right => do
    let (a, _) ← r.lookup left
    let some b := reference.types[right]? | throw "compiler comparison type absent"
    let go := sameType r reference fuel
    match a.shape, b.shape with
    | .bool, .bool | .char, .char | .str, .str => return true
    | .int x, .int y | .uint x, .uint y => return x == y
    | .rawPointer x xm, .rawPointer y ym => return xm == ym && (← go x y)
    | .reference x xm xr, .reference y ym yr => return xm == ym && xr == yr && (← go x y)
    | .tuple xs, .tuple ys =>
      if xs.size != ys.size then return false
      return (← (xs.zip ys).mapM fun (x,y) => go x y).all id
    | .dynamicTraitObject xs xp xr, .dynamicTraitObject ys yp yr =>
      if xr != yr || xs.size != ys.size then return false
      unless (xp.bind fun id => xs.findIdx? (· == id)) == (yp.bind fun id => ys.findIdx? (· == id)) do return false
      for (x,y) in xs.zip ys do
        let some a := r.predicates[x]? | throw "source predicate absent"
        let some b := reference.predicates[y]? | throw "compiler predicate absent"
        unless a.kind == b.kind && a.definitionPath == b.definitionPath &&
            a.boundVariables == b.boundVariables && a.genericArgs.size == b.genericArgs.size do return false
        for (x,y) in a.genericArgs.zip b.genericArgs do
          let .Type x := x | throw "source predicate argument unsupported"
          let .Type y := y | throw "compiler predicate argument unsupported"
          unless ← go x y do return false
        match a.projectionTerm, b.projectionTerm with
        | none, none => pure ()
        | some x, some y => unless ← go x y do return false
        | _, _ => return false
      return true
    | _, _ => return false

def main (paths : List String) : IO Unit := do
  let [mode, sourcePath, referencePath] := paths
    | throw (IO.userError "usage: FoundationReferenceArguments full|header SOURCE_JSON SCHEMA12_JSON")
  let d ← expect (Json.parse (← IO.FS.readFile sourcePath) >>= decode)
  let reference ← expect (Input.decodeJson (← IO.FS.readFile referencePath))
  let reference := reference.document
  let runtime ← expect ((Input.RuntimeMetadata.ofDocument reference).mapError toString)
  let (definition, compilerInstance) ← if mode == "header" then do
      let headers ← expect (d.source.getObjValAs? (Array Json) "source_function_signatures")
      let selected ← expect (headers.filterM fun h => do
        let id ← h.getObjValAs? Nat "definition"
        let some row := d.definitions[id]? | throw "header definition missing"
        return (← row.getObjValAs? String "path") == "std::rt::lang_start_internal")
      let some header := selected[0]? | throw (IO.userError "actual std header missing")
      check (selected.size == 1) "duplicate std header"
      let definition ← expect (header.getObjValAs? Nat "definition")
      let some compilerItem := reference.instances.find? (·.defPath == some "std::rt::lang_start_internal")
        | throw (IO.userError "actual std reference instance missing")
      pure (definition, compilerItem.id)
    else if mode == "full" then do
      let some body := d.bodies[0]? | throw (IO.userError "source body absent")
      let definition ← expect (body.getObjValAs? Nat "definition")
      let some root := reference.bodyRoots[0]? | throw (IO.userError "compiler root absent")
      pure (definition, root.entryInstance)
    else throw (IO.userError "unknown comparison mode")
  let (r, abi) ← expect (rustFunctionAbiOfSourceSignature d definition #[])
  let queries := reference.queries.instanceAbis.filter (fun q => q.instanceId == compilerInstance && q.extraArgumentTypes.isEmpty)
  check (queries.size == 1) "compiler ABI key missing or ambiguous"
  let some query := queries[0]? | throw (IO.userError "compiler ABI key absent")
  let some compilerAbi := reference.functionAbis[query.abiId]? | throw (IO.userError "compiler ABI absent")
  check (abi.arguments.size == compilerAbi.arguments.size) "ABI argument count differs"
  let sourceArguments := abi.arguments.push abi.returnValue
  let compilerArguments := compilerAbi.arguments.push compilerAbi.returnValue
  for (a,b) in sourceArguments.zip compilerArguments do
    check (← expect (sameType r reference 128 a.typeId b.typeId)) "semantic ABI type join differs"
    let some sourceLayout := r.layouts[a.layoutId]? | throw (IO.userError "source ABI physical row absent")
    let some compilerLayout := reference.layouts[b.layoutId]? | throw (IO.userError "compiler ABI physical row absent")
    let target ← expect (runtimeTargetOfTarget d.target)
    let x ← expect ((Input.RuntimeMetadata.layout target sourceLayout).mapError toString)
    let y ← expect ((Input.RuntimeMetadata.layout runtime.target compilerLayout).mapError toString)
    check (x == y) "complete ABI physical layout differs"
  let rebase (a b : Input.AbiArgument) := {a with typeId := b.typeId, layoutId := b.layoutId}
  let rebasedArguments := (abi.arguments.zip compilerAbi.arguments).map fun (a,b) => rebase a b
  let rebased : Input.FunctionAbi := {
    abi with
    arguments := rebasedArguments
    returnValue := rebase abi.returnValue compilerAbi.returnValue }
  check (rebased == compilerAbi) "complete source-derived FnAbi differs from compiler"
  let compilation ← expect (d.source.getObjVal? "compilation")
  let optimized := {d with source := d.source.setObjVal! "compilation" (compilation.setObjVal! "opt_level" (toJson "Aggressive"))}
  rejects (rustFunctionAbiOfSourceSignature optimized definition #[])
  let absentOpt := {d with source := d.source.setObjVal! "compilation" Json.null}
  rejects (rustFunctionAbiOfSourceSignature absentOpt definition #[])
  if mode == "header" then
    check (!(d.bodies.any fun body => (body.getObjValAs? Nat "definition").toOption == some definition)) "std header masquerades as executable body"
    rejects (rustFunctionAbiOfSourceSignature {d with source := d.source.setObjVal! "source_function_signatures" (.arr #[])} definition #[])
    rejects (rustFunctionAbiOfSourceSignature {d with source := d.source.setObjVal! "dyn_metadata_source" Json.null} definition #[])
  else
    let some body := d.bodies[0]? | throw (IO.userError "body source missing")
    let broken := {d with bodies := #[body.setObjVal! "locals" Json.null]}
    let _ ← expect (rustFunctionAbiOfSourceSignature broken definition #[])
  IO.println s!"{mode}: complete compiler FnAbi/type/layout comparison passed; unavailable/optimized source rejects"
