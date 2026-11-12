import Miri.Input.TableTail
import Miri.Input.StructuralNeedsDrop
import Lean.Data.Json.Printer

/-! Finite pinned-rustc differential. Baseline types supply instantiated source
material and normalization dependency IDs; baseline needs_drop answers are oracle
only. Definition flags and destructor identities come independently from the
fresh candidate export. Definitions crosswalk by rustc crate/index identity,
never diagnostic spelling. Unrelated ABI/MIR catalogs are not decoded. -/
open Lean Miri.Input

private def readTypes (value : Json) : Except String (Array TypeNode) := do
  let booleans ← value.getObjVal? "boolean_queries"
  let discriminants ← value.getObjVal? "discriminants"
  let pool ← JsonReader.run (JsonReader.array DecoderValues.booleanQueries) booleans.compress
  let discriminants ← JsonReader.run (JsonReader.array DecoderValues.parseDiscriminants) discriminants.compress
  let types ← value.getObjVal? "types"
  JsonReader.run (JsonReader.array (DecoderValues.parseTypeNode "$needs_drop.types" pool discriminants)) types.compress

private def definitions (value : Json) : Except String (Array DefinitionId) := do
  let rows ← value.getObjVal? "definitions"
  JsonReader.run (JsonReader.array (DecoderValues.parseDefinitionId "$needs_drop.definitions")) rows.compress

private def check (baseline candidate : Json) (richCoverage : Bool) : Except String String := do
  unless (← (← baseline.getObjVal? "schema_version").getNat?) == 12 do
    throw "expected canonical schema12 baseline"
  unless (← (← candidate.getObjVal? "schema_version").getNat?) == 13 do
    throw "expected current schema13 candidate"
  let nodes ← readTypes baseline
  let baseDefinitions ← definitions baseline
  let candidateDefinitions ← definitions candidate
  let node (id : Nat) : Except String TypeNode := do
    let some result := nodes[id]? | throw "baseline material type absent"
    unless result.id == id do throw "baseline material type identity mismatch"
    pure result
  let shape (id : Nat) : Except String TypeShape := do
    let some facts := (← node id).compilerFacts | throw "baseline normalization material absent"
    let some (_, some normalized) := facts.typeQueries.find? (·.1 == "normalized")
      | throw "baseline normalization dependency absent"
    pure (← node normalized).shape
  let adtMaterial (id : Nat) : Except String StructuralNeedsDrop.AdtMaterial := do
    let some identity := baseDefinitions[id]? | throw "baseline ADT identity absent"
    let matching := candidateDefinitions.filter fun d =>
      d.crateIndex == identity.crateIndex && d.index == identity.index
    unless matching.size == 1 do throw "candidate ADT definition crosswalk missing or ambiguous"
    let some definition := matching[0]? | throw "candidate ADT definition absent"
    let some material := definition.adtDrop | throw "candidate raw ADT drop material absent"
    if let some destructor := material.destructor then
      unless destructor < candidateDefinitions.size do throw "candidate destructor identity out of bounds"
    pure material
  let mut compared := 0
  let mut positive := 0
  let mut negative := 0
  let mut residual := 0
  let mut manual := 0
  let mut destructors := 0
  let mut unions := 0
  let mut zeroArrays := 0
  let mut nonzeroArrays := 0
  let mut closures := 0
  for source in nodes do
    let some facts := source.compilerFacts | throw "baseline needs_drop oracle absent"
    let some (_, expected) := facts.booleanQueries.find? (·.1 == "needs_drop")
      | throw "baseline needs_drop oracle missing"
    let actual ← StructuralNeedsDrop.query shape adtMaterial (nodes.size + 1) source.id
    let some actual := actual | do
      residual := residual + 1
      continue
    unless actual == expected do
      throw s!"type {source.id}: Lean needs_drop={actual}, rustc={expected}"
    compared := compared + 1
    if actual then positive := positive + 1 else negative := negative + 1
    match source.shape with
    | .adt data =>
      let material ← adtMaterial data.definition
      if material.manuallyDrop then manual := manual + 1
      if material.destructor.isSome then destructors := destructors + 1
      if data.kind == .unionKind then unions := unions + 1
    | .array _ _ constructor =>
      if constructor.count == 0 then zeroArrays := zeroArrays + 1 else nonzeroArrays := nonzeroArrays + 1
    | .closure .. | .coroutineClosure .. => closures := closures + 1
    | _ => pure ()
  if richCoverage then
    unless positive > 0 && negative > 0 && manual > 0 && destructors > 0 && unions > 0 &&
        zeroArrays > 0 && nonzeroArrays > 0 && closures > 0 do
      throw "needs_drop fixture lacks required positive/negative/ADT/array/closure coverage"
  else
    unless positive == 0 && negative >= 29 && residual == 0 do
      throw "no-drop DAG comparison requires at least 29 resolved negative type queries"
  let candidateNodes ← readTypes candidate
  let eager := candidateNodes.filter fun source => source.compilerFacts.any fun facts =>
    facts.booleanQueries.any (·.1 == "needs_drop")
  pure s!"PASS {compared} rustc/Lean needs_drop comparisons; true={positive}, false={negative}, residual={residual}, manual={manual}, destructor={destructors}, union={unions}, zero_array={zeroArrays}, nonzero_array={nonzeroArrays}, closure={closures}; candidate eager rows={eager.size}/{candidateNodes.size}"

def main (args : List String) : IO Unit := do
  let (baselinePath, candidatePath, richCoverage) ← match args with
    | [baseline, candidate] => pure (baseline, candidate, true)
    | [baseline, candidate, "--no-drop-dag"] => pure (baseline, candidate, false)
    | _ => throw (IO.userError "usage: CompareNeedsDrop BASELINE.json CANDIDATE.json [--no-drop-dag]")
  let baseline ← match Json.parse (← IO.FS.readFile baselinePath) with
    | .ok value => pure value | .error error => throw (IO.userError error)
  let candidate ← match Json.parse (← IO.FS.readFile candidatePath) with
    | .ok value => pure value | .error error => throw (IO.userError error)
  match check baseline candidate richCoverage with
  | .ok result => IO.println result
  | .error error => throw (IO.userError error)
