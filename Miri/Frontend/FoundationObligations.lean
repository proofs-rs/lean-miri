import Miri.Frontend.Foundation
import Miri.Frontend.FoundationGenericEnvironment
import Miri.Frontend.FoundationTraitClaims
import Miri.Frontend.FoundationTermination
import Miri.Frontend.FoundationExistentialBounds
import Miri.Frontend.FoundationFnSupertraits
import Miri.Frontend.FoundationOutlives
import Miri.Frontend.FoundationProjectionClauses

/-! Pure checks for the small set of obligations understood by the restricted
foundation fixture evaluator. Unknown traits and forms remain errors. -/

namespace Miri.Frontend.Foundation
open Lean

private def field (j : Json) (key : String) : Except String Json := j.getObjVal? key
private def str (j : Json) (key : String) : Except String String := j.getObjValAs? String key
private def num (j : Json) (key : String) : Except String Nat := j.getObjValAs? Nat key
private def arr (j : Json) (key : String) : Except String (Array Json) := j.getObjValAs? (Array Json) key

private def scalarType : ConcreteType → Bool
  | .primitive "bool" "" | .primitive "char" "" => true
  | .primitive "uint" _ | .primitive "int" _ | .primitive "float" _ => true
  | _ => false

private def sizedAndCopy : Nat → ConcreteType → Bool
  | 0, _ => false
  | f+1, ty => if scalarType ty then true else match ty with
    -- Pinned candidate_assembly.rs gives FnPtr unconditional builtin
    -- Copy/Clone and Sized candidates (select/mod.rs has no constituents).
    | .functionPointer .. => true
    | .array element _ => sizedAndCopy f element
    | .tuple elements => elements.all (sizedAndCopy f)
    -- The source graph currently drops pointer mutability at substitution.
    -- In particular, &mut T is not Copy, so pointer obligations stay unknown.
    | .pointer _ _ => false
    | _ => false

private def ensureParam (typeArgs : Array (Option ConcreteType))
    (constArgs : Array (Option Nat)) (param : Json) : Except String Unit := do
  let index ← num param "index"
  match ← str param "kind" with
  | "type" =>
    unless (typeArgs[index]?.bind id).isSome && (constArgs[index]?.bind id).isNone do
      throw s!"missing or wrong-kind type argument {index}"
  | "const" =>
    unless (constArgs[index]?.bind id).isSome && (typeArgs[index]?.bind id).isNone do
      throw s!"missing or wrong-kind const argument {index}"
  | other => throw s!"unsupported generic parameter {other}"

/-- Check every emitted generic predicate for the recognized primitive/array
domain.  This is a pure, deliberately incomplete trait solver. -/
def checkEnvironment (d : Document) (typeArgs : Array (Option ConcreteType))
    (constArgs : Array (Option Nat)) (environment : Json) : Except String Unit := do
  let environment ← flattenEnvironment d environment
  let parameters ← arr environment "parameters"
  for param in parameters do ensureParam typeArgs constArgs param
  for (entry, index) in typeArgs.toList.zipIdx do
    if entry.isSome then
      unless parameters.any (fun p =>
          (num p "index").toOption == some index && (str p "kind").toOption == some "type") do
        throw s!"unexpected type argument {index}"
  for (entry, index) in constArgs.toList.zipIdx do
    if entry.isSome then
      unless parameters.any (fun p =>
          (num p "index").toOption == some index && (str p "kind").toOption == some "const") do
        throw s!"unexpected const argument {index}"
  for clause in (← arr environment "clauses") do
    match ← str clause "kind" with
    | "trait" =>
      let definition ← num clause "definition"
      let some row := d.definitions[definition]? | throw "unknown trait definition"
      let path ← str row "path"
      let arguments ← arr clause "arguments"
      let some arg := arguments[0]? | throw "missing trait self argument"
      unless (← str arg "kind") == "type" do throw "non-type trait self argument"
      let source ← typeExpr d (← num arg "type")
      let ty ← instantiate typeArgs constArgs source
      if let .dynamicObject existential := ty then
        let mut traitArguments := #[]
        for argument in arguments.extract 1 arguments.size do
          unless (← str argument "kind") == "type" do throw "non-type dynamic trait argument unsupported"
          traitArguments := traitArguments.push (← instantiate typeArgs constArgs (← typeExpr d (← num argument "type")))
        checkSourceExistentialTrait d existential definition traitArguments
        continue
      if let .functionPointer .. := ty then
        if arguments.size == 2 then
          let mut traitArguments := #[]
          for argument in arguments.extract 1 arguments.size do
            unless (← str argument "kind") == "type" do throw "non-type Fn trait argument unsupported"
            traitArguments := traitArguments.push (← instantiate typeArgs constArgs (← typeExpr d (← num argument "type")))
          checkFunctionPointerFnTrait d definition ty traitArguments
          continue
      unless arguments.size == 1 do throw "unsupported trait argument count"
      if path == "std::marker::Copy" || path == "std::marker::Sized" ||
          path == "core::marker::Copy" || path == "core::marker::Sized" then
        unless sizedAndCopy 1024 ty do throw s!"unresolved trait obligation {path}"
      else if ((d.source.getObjVal? "termination_source" >>= fun s => s.getObjValAs? Nat "definition").toOption == some definition) then
        let _ ← sourceTerminationUnitSelection d definition ty
      else
        unless (← localTraitClaim row ty) do throw s!"unsatisfied local trait obligation {path}"
    | "projection" => checkProjectionClause d typeArgs constArgs clause
    | "type_outlives" =>
      let ty ← instantiate typeArgs constArgs (← typeExpr d (← num clause "type"))
      checkStaticOutlives ty (← str clause "region")
    | "const_has_type" =>
      let ty ← instantiate typeArgs constArgs (← typeExpr d (← num clause "type"))
      let .primitive "uint" "usize" := ty | throw "unsupported const parameter type"
      let value ← field clause "value"
      let n ← match ← str value "kind" with
        | "param" =>
          let index ← num value "index"
          let some n := constArgs[index]?.bind id | throw "unbound const parameter"
          pure n
        | "value" =>
          let bits ← str value "bits"
          let some n := bits.toNat? | throw "invalid const scalar"
          pure n
        | _ => throw "unsupported const parameter expression"
      unless n < 2 ^ d.target.pointerSizeBits do throw "const parameter exceeds usize"
    | other => throw s!"unsupported foundation predicate {other}"

end Miri.Frontend.Foundation
