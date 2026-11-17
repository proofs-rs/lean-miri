import Miri.Input.Decoder
import Miri.Input.CallResolution
import MiriTests.Input.OracleAbi
import Miri.Input.SourceAbiRuntime
import Miri.Input.ConcreteCastQueries

open Miri.Input

private structure OracleRow where
  key : Nat
  extra : Array TypeId
  abi : OracleAbi.FunctionAbi

private structure Oracle where
  layouts : Array Layout
  instances : Array OracleRow
  pointers : Array OracleRow
  excluded : Array (Nat × String)

private def parseRow (key : String) : JsonReader.Parser OracleRow := do
  let (subject, extra, abi) ← JsonReader.object (none, none, none) fun (subject, extra, abi) field => do
    if field == key then return (some (← JsonReader.natural), extra, abi)
    match field with
    | "extra_argument_types" => return (subject, some (← JsonReader.array JsonReader.natural), abi)
    | "abi" => return (subject, extra, some (← OracleAbi.parseFunctionAbi "$oracle.abi"))
    | _ => JsonReader.skipValue; return (subject, extra, abi)
  return ⟨← JsonReader.required subject key, ← JsonReader.required extra "extra_argument_types",
    ← JsonReader.required abi "abi"⟩

private def parseOracle : JsonReader.Parser Oracle := do
  let value ← JsonReader.object (none : Option Oracle) fun value key => do
    if key != "abi" then JsonReader.skipValue; return value
    let (layouts, instances, pointers, excluded) ← JsonReader.object (none, none, none, none)
        fun (layouts, instances, pointers, excluded) key => do
      match key with
      | "abi_layouts" => return (some (← JsonReader.array (DecoderValues.parseLayout "$oracle.abi_layouts")), instances, pointers, excluded)
      | "instances" => return (layouts, some (← JsonReader.array (parseRow "instance_id")), pointers, excluded)
      | "pointers" => return (layouts, instances, some (← JsonReader.array (parseRow "type_id")), excluded)
      | "excluded_pointers" =>
        let rows ← JsonReader.array do
          let (key, reason) ← JsonReader.object (none, none) fun (key, reason) field => do
            match field with
            | "type_id" => return (some (← JsonReader.natural), reason)
            | "reason" => return (key, some (← JsonReader.string))
            | _ => JsonReader.skipValue; return (key, reason)
          pure (← JsonReader.required key "type_id", ← JsonReader.required reason "reason")
        return (layouts, instances, pointers, some rows)
      | _ => JsonReader.skipValue; return (layouts, instances, pointers, excluded)
    return some ⟨← JsonReader.required layouts "abi_layouts", ← JsonReader.required instances "instances",
      ← JsonReader.required pointers "pointers", ← JsonReader.required excluded "excluded_pointers"⟩
  JsonReader.required value "abi"

def main (args : List String) : IO UInt32 := do
  let [path, oraclePath] := args | throw (IO.userError "usage: CheckSourceAbi <fresh-export.json> <oracle.json>")
  let input ← match ← decodeFile path with
    | .ok input => pure input
    | .error reason => throw (IO.userError s!"input decode failed: {reason}")
  let document := input.document
  let oracle ← IO.FS.readFile oraclePath
  let oracle ← match JsonReader.run parseOracle oracle with
    | .ok oracle => pure oracle
    | .error reason => throw (IO.userError s!"oracle decode failed: {reason}")
  let runtime ← match RuntimeMetadata.ofDocument document with
    | .ok runtime => pure runtime
    | .error reason => throw (IO.userError s!"target decode failed: {reason}")
  let program ← match lowerProgram document with
    | .ok program => pure program
    | .error reason => throw (IO.userError s!"MIR lowering failed: {reason}")
  let context : CompilerFacts.Context := ⟨runtime, program, none⟩
  for (key, reason) in oracle.excluded do
    unless reason == "escaping_bound_variables" do throw (IO.userError "unknown ABI oracle exclusion reason")
    let _ ← match runtime.node key with
      | .ok node => pure node
      | .error reason => throw (IO.userError s!"excluded oracle type is absent: {reason}")
    match ConcreteCastQueries.noBoundVars runtime #[.Type key] with
    | .ok false => pure ()
    | _ => throw (IO.userError s!"oracle excluded valid concrete type {key}")
    unless !(document.bodies.any fun body => body.mir.locals.contains key ||
        body.callEvidence.any (fun evidence => evidence.any (·.functionType == some key))) do
      throw (IO.userError s!"oracle excluded an actual MIR function type {key}")
    IO.println s!"source ABI excluded metadata FnPtr {key}: {reason}"
  let mut checked := 0
  let mut errors := 0
  let mut higherRanked := 0
  for row in oracle.instances do
    let actual := SourceAbiRuntime.ofInstance context.runtime row.key row.extra
    let expected := OracleAbi.functionAbi runtime oracle.layouts row.abi
    match actual, expected with
    | .ok actual, .ok expected =>
      checked := checked + 1
      unless actual == expected do
        errors := errors + 1
        IO.println s!"instance {row.key} extra={reprStr row.extra}: ABI differs\ncomputed={reprStr actual}\nrustc={reprStr expected}"
    | .error reason, _ =>
      errors := errors + 1
      IO.println s!"instance {row.key}: calculation failed: {reason}"
    | _, .error reason =>
      errors := errors + 1
      IO.println s!"instance {row.key}: compiler oracle decode failed: {reason}"
  for row in oracle.pointers do
    if let .ok node := runtime.node row.key then
      if let .functionPointer _ binders := node.shape then
        unless binders.isEmpty do higherRanked := higherRanked + 1
    let actual := do
      let node ← runtime.node row.key |>.mapError toString
      let .functionPointer signature _ := node.shape | throw "oracle pointer type is not FnPtr"
      SourceAbiRuntime.ofSignature context.runtime signature row.extra
    let expected := OracleAbi.functionAbi runtime oracle.layouts row.abi
    match actual, expected with
    | .ok actual, .ok expected =>
      checked := checked + 1
      unless actual == expected do
        errors := errors + 1
        IO.println s!"pointer {row.key} extra={reprStr row.extra}: ABI differs\ncomputed={reprStr actual}\nrustc={reprStr expected}"
    | .error reason, _ | _, .error reason =>
      errors := errors + 1
      IO.println s!"pointer {row.key}: {reason}"
  IO.println s!"source ABI: compared={checked}, failures={errors}; finite no_deduced_attrs compiler comparison only; excluded={oracle.excluded.size}; higher-ranked FnPtr comparisons={higherRanked}"
  if checked == 0 && errors == 0 && document.bodies.isEmpty && !document.rootDeclarations.isEmpty then
    IO.println "source ABI: not applicable: declaration-only input"
    return 0
  return if errors == 0 && checked > 0 then 0 else 1
