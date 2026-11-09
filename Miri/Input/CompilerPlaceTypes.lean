import Miri.Input.CompilerFrameContext

/-! Exact debug-only place/operand type checks, place.rs:626–643 and
operand.rs:805–830. The compiler's instantiated body supplies each expected
place type. Runtime projection/layouts never substitute for that query. -/
namespace Miri.Input.CompilerPlaceTypes
open Lean Miri.ABI Miri.Interpreter Miri.Memory

private def fields? : TypedValue → Option (Array (String × TypedValue))
  | .object fields | .statement _ fields | .terminator _ fields | .rvalue _ fields
  | .operand _ fields | .projection _ fields | .enumTag _ _ fields => some fields
  | _ => none

private def field (fields : Array (String × TypedValue)) (name : String) : Except String TypedValue :=
  match fields.find? (·.1 == name) with
  | some (_,value) => pure value
  | none => throw s!"normalized query changed source field {name}"

private partial def scan (ctx : LowerContext) (requested : MIR.Place)
    (source normalized : TypedValue) : Except String (Array MIR.TyId) := do
  let mut found := #[]
  if let some sourceFields := fields? source then
    let some normalizedFields := fields? normalized
      | throw "normalization changed source place container kind"
    if sourceFields.any (·.1 == "local") && sourceFields.any (·.1 == "projection") then
      let key ← lowerCompilerPlace ctx source
      if key == requested then
        let .typeRef typeId ← field normalizedFields "type"
          | throw "normalized place has no typed compiler type"
        found := found.push typeId
    for (key,value) in sourceFields do
      if (fields? value).isSome || (match value with | .array _ => true | _ => false) then
        found := found ++ (← scan ctx requested value (← field normalizedFields key))
  else if let .array values := source then
    let .array counterparts := normalized
      | throw "normalization changed source place container kind"
    unless values.size == counterparts.size do throw "normalization changed source place container length"
    for index in [:values.size] do
      let some original := values[index]? | throw "source traversal index absent"
      let some actual := counterparts[index]? | throw "normalized traversal index absent"
      found := found ++ (← scan ctx requested original actual)
  pure found

def expectedLayout (p : CompilerProviders.Prepared) (frame : CompilerFrameContext.ActualFrame)
    (requested : MIR.Place) : Except String LocalLayout := do
  let body ← CompilerFrameContext.bodyOfFrame p frame
  let normalized ← CompilerFrameContext.normalizedBody p frame
  unless body.input.blocks.size == normalized.blocks.size do
    throw "normalization changed source block count"
  let mut ids := #[]
  for index in [:body.input.blocks.size] do
    let some source := body.input.blocks[index]? | throw "source traversal index absent"
    let some actual := normalized.blocks[index]? | throw "normalized traversal index absent"
    unless source.statements.size == actual.statements.size do
      throw "normalization changed source statement count"
    for statementIndex in [:source.statements.size] do
      let some original := source.statements[statementIndex]? | throw "source statement absent"
      let some counterpart := actual.statements[statementIndex]? | throw "normalized statement absent"
      ids := ids ++ (← scan p.loweringContext requested original.value counterpart.value)
    ids := ids ++ (← scan p.loweringContext requested source.terminator.value actual.terminator.value)
  let some id := ids[0]? | throw "place has no exact compiler normalization evidence in canonical body"
  unless ids.all (· == id) do throw "same source place has conflicting normalized compiler types"
  p.runtime.lookup id |>.mapError toString

def check (p : CompilerProviders.Prepared) (debugAssertions : Bool)
    (relateCovariantly : LocalLayout → LocalLayout → MachineHooks.M K U Bool)
    (requested : MIR.Place) (actual : LocalLayout) : MachineHooks.M K U Unit := do
  if !debugAssertions then return
  let expected ← match expectedLayout p (← MachineHooks.currentFrame) requested with
    | .ok value => pure value
    | .error reason => throw (.unsupported s!"compiler place type query: {reason}")
  let related ← if expected.ty == actual.ty then pure true else relateCovariantly expected actual
  unless related do throw (.invalidProgram "MIR place compiler type differs from evaluated place type")
  unless expected.layout == actual.layout do
    throw (.invalidProgram "MIR covariant assignment has different compiler layouts")

def operand (p : CompilerProviders.Prepared) (debugAssertions : Bool)
    (relateCovariantly : LocalLayout → LocalLayout → MachineHooks.M K U Bool)
    (_ : C) (requested : MIR.Place) (value : OpTy Provenance) : MachineHooks.M K U Unit :=
  check p debugAssertions relateCovariantly requested value.layout

def place (p : CompilerProviders.Prepared) (debugAssertions : Bool)
    (relateCovariantly : LocalLayout → LocalLayout → MachineHooks.M K U Bool)
    (_ : C) (requested : MIR.Place) (value : RuntimePlace Provenance) : MachineHooks.M K U Unit :=
  check p debugAssertions relateCovariantly requested value.layout
end Miri.Input.CompilerPlaceTypes
