import Miri.Frontend.FoundationTypeRegistry
import Miri.Frontend.FoundationRegionErasure
import Miri.Frontend.FoundationFnVtable

/-! Projection equality source and a narrow FnPtr/FnOnce::Output check. No
associated-type normalization, inference, or arbitrary trait selection occurs. -/
namespace Miri.Frontend.Foundation
open Lean
structure ProjectionClauseSource where
  definition : Nat
  parentTrait : Nat
  arguments : Array TypeExpr
  term : TypeExpr

private def definitionRow (document : Document) (id : Nat) (kind : String) : Except String Json := do
  let some row := document.definitions[id]? | throw "projection definition absent"
  unless (← row.getObjValAs? Nat "definition_id") == id &&
      (← row.getObjValAs? String "kind") == kind do throw "projection definition identity/kind mismatch"
  return row

/-- Decode all ordered arguments and the equality term; no omitted binder or
parent identity can be replaced by a guessed empty/default declaration. -/
def projectionClauseSource (document : Document) (source : Json) : Except String ProjectionClauseSource := do
  unless (← source.getObjValAs? String "kind") == "projection" do throw "projection clause kind mismatch"
  unless (← source.getObjValAs? (Array Json) "bound_variables").isEmpty do
    throw "bound projection clause unsupported"
  let definition ← source.getObjValAs? Nat "definition"
  let row ← definitionRow document definition "AssocTy"
  let parentTrait ← source.getObjValAs? Nat "parent_trait"
  let _ ← definitionRow document parentTrait "Trait"
  let declaration ← row.getObjVal? "associated_type"
  unless (← declaration.getObjValAs? Nat "parent_trait") == parentTrait do
    throw "projection parent trait identity mismatch"
  let arguments ← source.getObjValAs? (Array Json) "arguments"
  unless arguments.size == (← declaration.getObjValAs? Nat "parent_count") +
      (← declaration.getObjValAs? Nat "own_parameter_count") do throw "projection source argument count mismatch"
  let arguments ← arguments.mapM fun argument => do
    unless (← argument.getObjValAs? String "kind") == "type" do throw "projection non-type argument unsupported"
    typeExpr document (← argument.getObjValAs? Nat "type")
  let term ← source.getObjVal? "term"
  unless (← term.getObjValAs? String "kind") == "type" do throw "projection const term unsupported"
  return { definition, parentTrait, arguments, term := ← typeExpr document (← term.getObjValAs? Nat "type") }

/-- Structural builtin FnOnce equality for a known safe Rust FnPtr only.
Closures, dynamic objects, aliases and unresolved signatures remain unsupported.
The complete Fn source declaration graph establishes the associated identity. -/
def checkProjectionClause (document : Document) (types : Array (Option ConcreteType))
    (constants : Array (Option Nat)) (source : Json) : Except String Unit := do
  let clause ← projectionClauseSource document source
  let declarations ← readFnVtableDeclarations document.source
  let fnOnce ← fnSourceRoot declarations "fn_once"
  let _ ← fnVtableCandidates declarations fnOnce
  unless clause.parentTrait == fnOnce do throw "projection trait outside builtin FnOnce source rule"
  let row ← fnSourceDeclaration declarations fnOnce
  let outputs ← (← row.getObjValAs? (Array Json) "associated_items").filterM fun item =>
    return (← item.getObjValAs? String "kind") == "type" && (← item.getObjValAs? String "name") == "Output"
  let [output] := outputs.toList | throw "FnOnce Output source identity missing or duplicated"
  unless clause.definition == (← output.getObjValAs? Nat "definition") do throw "projection is not exact FnOnce Output"
  let arguments ← clause.arguments.mapM fun argument => instantiate types constants argument >>= eraseRegions
  let [pointer, tuple] := arguments.toList | throw "FnOnce projection argument count mismatch"
  let .functionPointer inputs actualOutput "safe" "rust" false := pointer
    | throw "FnOnce projection Self is not supported function pointer"
  let expectedOutput ← eraseRegions (← instantiate types constants clause.term)
  unless sameConcrete 1024 (.tuple inputs) tuple && sameConcrete 1024 actualOutput expectedOutput do
    throw "FnOnce projection tuple/Output equality mismatch"

/-- The builtin Fn-family tuple premise for a safe Rust function pointer.
This establishes only this trait header, not caller parent obligations. -/
def checkFunctionPointerFnTrait (document : Document) (definition : Nat)
    (pointer : ConcreteType) (arguments : Array ConcreteType) : Except String Unit := do
  let declarations ← readFnVtableDeclarations document.source
  let roots ← #["fn", "fn_mut", "fn_once"].mapM (fnSourceRoot declarations)
  unless roots.contains definition do throw "function-pointer trait outside Fn source family"
  let _ ← fnVtableCandidates declarations definition
  let .functionPointer inputs _ "safe" "rust" false ← eraseRegions pointer
    | throw "builtin Fn Self is not supported safe Rust function pointer"
  let [tuple] := arguments.toList | throw "builtin Fn tuple argument missing or extra"
  unless sameConcrete 1024 (.tuple inputs) (← eraseRegions tuple) do
    throw "builtin Fn tuple argument mismatch"

end Miri.Frontend.Foundation
