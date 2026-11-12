import Miri.Input.GenericSubstitution
import Miri.Input.JsonReader

/-! Decoder for raw early-bound source templates. Definition identities are
compiler crate/index pairs, independently of display names and runtime TyIds. -/
namespace Miri.Input.GenericMaterialCodec
open Lean GenericSubstitution

def readSort (value : Json) : Except String ArgSort := do
  match ← value.getStr? with
  | "type" => pure .type | "region" => pure .region
  | "constant" => pure .constant | "aggregate" => pure .aggregate
  | _ => throw "unknown generic material sort"

def readDefinition (value : Json) : Except String DefinitionIdentity := do
  let crateIndex ← (← value.getObjVal? "crate").getNat?
  let index ← (← value.getObjVal? "index").getNat?
  unless crateIndex < 2^32 && index < 2^32 do throw "generic definition identity exceeds u32"
  pure ⟨crateIndex, index⟩

def readIdentity (value : Json) : Except String BoundIdentity := do
  match ← (← value.getObjVal? "kind").getStr? with
  | "anonymous" => pure .anonymous
  | "named" => return .named (← readDefinition (← value.getObjVal? "definition"))
  | "named_for_printing" => return .namedForPrinting (← (← value.getObjVal? "name").getStr?)
  | "closure_environment" => pure .closureEnvironment
  | _ => throw "unknown generic bound identity"

def readVariable (value : Json) : Except String BoundVariable := do
  match ← (← value.getObjVal? "kind").getStr? with
  | "type" => return .type (← readIdentity (← value.getObjVal? "identity"))
  | "region" => return .region (← readIdentity (← value.getObjVal? "identity"))
  | "constant" => pure .constant
  | _ => throw "unknown generic bound variable sort"

def readTerm : Nat → Json → Except String GenericSubstitution.Term
  | 0, _ => .error "generic material parser depth exhausted"
  | fuel + 1, value => do
    let natural (key : String) : Except String Nat := do
      let n ← (← value.getObjVal? key).getNat?
      unless n < 2^32 do throw "generic material variable index exceeds u32"
      pure n
    let string (key : String) := do (← value.getObjVal? key).getStr?
    let sort := do readSort (← value.getObjVal? "sort")
    match ← string "kind" with
    | "parameter" => return .parameter (← sort) (← natural "index")
    | "bound" => do
      let raw ← value.getObjVal? "index"
      let index : Miri.MIR.BoundVarIndexKind ← if raw == .null then pure .Canonical
        else do
          let n ← raw.getNat?
          unless n < 2^32 do throw "generic bound deBruijn index exceeds u32"
          pure (.Bound n)
      return .bound (← sort) index (← natural "variable") (← readIdentity (← value.getObjVal? "identity"))
    | "placeholder" => return .placeholder (← sort) (← natural "universe") (← natural "variable") (← readIdentity (← value.getObjVal? "identity"))
    | "inference" => return .inference (← sort) (← natural "variable")
    | "atom" => return .atom (← sort) (← string "tag") (← string "payload")
    | "node" => do
      let children ← (← value.getObjVal? "children").getArr?
      return .node (← sort) (← string "tag") (← string "payload")
        (Terms.ofArray (← children.mapM (readTerm fuel)))
    | "definition" => do
      let children ← (← value.getObjVal? "children").getArr?
      return .definition (← sort) (← string "tag") (← readDefinition (← value.getObjVal? "definition"))
        (Terms.ofArray (← children.mapM (readTerm fuel)))
    | "binder" => do
      let variables ← (← value.getObjVal? "variables").getArr?
      return .binder (← variables.mapM readVariable) (← readTerm fuel (← value.getObjVal? "value"))
    | other => throw s!"unknown generic material node {other}"

def validateParameters (parameters : Array ArgSort) : Nat → GenericSubstitution.Term → Except String Unit
  | 0, _ => .error "generic template parameter validation exhausted"
  | fuel + 1, term => do
    match term with
    | .parameter sort index =>
      let some expected := parameters[index]? | throw "generic template parameter is out of bounds"
      unless sort == expected do throw "generic template parameter has incorrect sort"
    | .binder _ body => validateParameters parameters fuel body
    | .node _ _ _ children | .definition _ _ _ children =>
      let _ ← children.mapM fun child => do
        validateParameters parameters fuel child
        pure child
      pure ()
    | _ => pure ()

def readTemplate (value : Json) : Except String DefinitionTemplate := do
  let parameters ← (← (← value.getObjVal? "parameters").getArr?).mapM readSort
  unless parameters.all (· != .aggregate) do throw "aggregate cannot be a generic parameter sort"
  let typeExpression ← readTerm 1024 (← value.getObjVal? "type_expression")
  unless typeExpression.sort == .type do throw "generic type template has non-type root"
  validateParameters parameters 1024 typeExpression
  let signature ← value.getObjVal? "signature_expression"
  let signatureExpression ← if signature == .null then pure none else do
    let term ← readTerm 1024 signature
    unless term.sort == .aggregate do throw "generic signature template has non-signature root"
    validateParameters parameters 1024 term
    pure (some term)
  let fields ← (← value.getObjVal? "fields").getArr?
  let fields ← fields.mapM fun field => do
    let variantIndex ← (← field.getObjVal? "variant").getNat?
    let fieldIndex ← (← field.getObjVal? "field").getNat?
    let expression ← readTerm 1024 (← field.getObjVal? "expression")
    unless expression.sort == .type do throw "generic field template has non-type root"
    validateParameters parameters 1024 expression
    pure ({variantIndex, fieldIndex, expression} : FieldTemplate)
  let mut seen := #[]
  for field in fields do
    let key := (field.variantIndex, field.fieldIndex)
    unless !seen.contains key do throw "generic field template is duplicated"
    seen := seen.push key
  pure {parameters, typeExpression, signatureExpression, fields}

def decodeTemplate : JsonReader.Parser DefinitionTemplate := do
  -- `any` asserts EOF and is only valid for a standalone JSON document.
  -- A definition template is one nested value in the streaming root decoder.
  JsonReader.liftExcept (readTemplate (← Lean.Json.Parser.anyCore))

end Miri.Input.GenericMaterialCodec
