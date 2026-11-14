import Miri.Input.Model.Types
import Miri.Input.VarianceInference

namespace Miri.Input.VarianceMaterial
open GenericSubstitution

private def identityArguments (parameters : Array ArgSort) (arguments : Terms) : Except String Unit := do
  let rec values : Terms → Array Term
    | .nil => #[] | .cons value rest => #[value] ++ values rest
  let arguments := values arguments
  unless arguments.size == parameters.size do throw "variance source identity argument count mismatch"
  for (parameter,index) in parameters.zipIdx do
    unless arguments[index]? == some (.parameter parameter index) do
      throw "variance source declaration does not have its identity arguments"

def definition (definitions : Array DefinitionId) (identity : DefinitionIdentity) :
    Except String DefinitionId := do
  let matching := definitions.filter fun source =>
    source.crateIndex == identity.crateIndex && source.index == identity.index
  unless matching.size == 1 do throw "variance source definition is absent or ambiguous"
  let some source := matching[0]? | throw "variance source definition disappeared"
  if source.adtDeclaration.isSome && source.aliasDeclaration.isSome then
    throw "variance source combines ADT and alias declaration roles"
  let hasSignature := source.genericTemplate.any (·.signatureExpression.isSome)
  if source.sourceEnvironment.any (·.isTrait) &&
      (source.adtDeclaration.isSome || source.aliasDeclaration.isSome || hasSignature) then
    throw "variance source combines trait and value/type declaration roles"
  if source.aliasDeclaration.isSome then
    if source.genericTemplate.any (fun template =>
        template.signatureExpression.isSome || !template.fields.isEmpty) then
      throw "variance alias source carries function signature or ADT fields"
  pure source

/-- These are source-declaration joins, not inference results. Families without
the declaration-kind material needed to verify their role stay unsupported. -/
private def validateRoles (definitions : Array DefinitionId) : Nat → Term → Except String Unit
  | 0, _ => throw "variance declaration-role traversal exhausted"
  | fuel + 1, term => do
    let visit := validateRoles definitions fuel
    let rec visitChildren : Terms → Except String Unit
      | .nil => pure () | .cons value rest => do visit value; visitChildren rest
    match term with
    | .definition .type "foreign" _ _ =>
      throw "foreign variance source requires an explicit raw declaration-kind witness"
    | .definition .type tag identity arguments =>
      if tag.startsWith "alias_" then
        let source ← definition definitions identity
        let some alias := source.aliasDeclaration | throw "variance alias source role is absent"
        unless alias.definition == identity do throw "variance alias source physical identity mismatch"
        if tag == "alias_free_rigid" || tag == "alias_free_not_rigid" then
          let .free _ := alias.kind | throw "free variance alias has an associated source role"
        else if tag == "alias_projection_rigid" || tag == "alias_projection_not_rigid" then
          let .associated container _ _ _ := alias.kind
            | throw "projection variance alias lacks an associated source role"
          if let .inherentImpl := container then throw "projection variance alias has an inherent source role"
        else if tag == "alias_inherent_rigid" || tag == "alias_inherent_not_rigid" then
          let .associated .inherentImpl _ _ _ := alias.kind
            | throw "inherent variance alias lacks an inherent source role"
        else throw "opaque variance alias declaration material is unavailable"
      visitChildren arguments
    | .definition .constant _ _ _ =>
      throw "constant-alias variance requires raw constant declaration-kind material"
    | .definition .aggregate tag identity arguments =>
      if tag == "trait" || tag == "auto_trait" then
        let source ← definition definitions identity
        unless source.sourceEnvironment.any (·.isTrait) do throw "variance existential trait source role mismatch"
      else if tag == "projection" then
        let source ← definition definitions identity
        let some alias := source.aliasDeclaration | throw "variance existential projection source role is absent"
        let .associated _ _ _ _ := alias.kind
          | throw "variance existential projection has a free source role"
      visitChildren arguments
    | .binder _ body => visit body
    | .node .constant _ _ _ => pure ()
    | .node _ _ _ arguments => visitChildren arguments
    | _ => pure ()

def declaration (definitions : Array DefinitionId) (identity : DefinitionIdentity) :
    Except String VarianceInference.Declaration := do
  let source ← definition definitions identity
  let some template := source.genericTemplate | throw "variance generic source template is absent"
  for field in template.fields do validateRoles definitions 16384 field.expression
  if let some signature := template.signatureExpression then validateRoles definitions 16384 signature
  if let some adt := source.adtDeclaration then
    adt.validate template
    unless template.signatureExpression.isNone do throw "ADT variance source carries a function signature"
    let .definition .type "adt" actual arguments := template.typeExpression
      | throw "ADT variance template has a non-ADT type expression"
    unless actual == identity do throw "ADT variance template physical identity mismatch"
    identityArguments template.parameters arguments
    pure ⟨template.parameters,template.fields.map (·.expression),none,adt.langItem⟩
  else
    let some signature := template.signatureExpression | throw "variance declaration is neither ADT nor function"
    unless template.fields.isEmpty do throw "function variance source carries ADT fields"
    let .definition .type "function_definition" actual
        (.cons (.binder variables (.node .aggregate "arguments" "" arguments)) .nil) := template.typeExpression
      | throw "function variance template has a non-function type expression"
    unless actual == identity do throw "function variance template physical identity mismatch"
    unless variables.isEmpty do throw "function variance declaration identity has bound generic arguments"
    identityArguments template.parameters arguments
    pure ⟨template.parameters,#[],some signature,none⟩

def expandAlias (definitions : Array DefinitionId) (identity : DefinitionIdentity)
    (arguments : Array Term) : Except String Term := do
  let source ← definition definitions identity
  let some alias := source.aliasDeclaration | throw "variance free alias declaration is absent"
  unless alias.definition == identity do throw "variance free alias physical identity mismatch"
  let .free _ := alias.kind | throw "variance free alias has an associated declaration"
  unless alias.hasValue do throw "variance free alias has no source RHS"
  let some template := source.genericTemplate | throw "variance free alias source template is absent"
  validateRoles definitions 16384 template.typeExpression
  let result ← template.instantiateType 16384 arguments
  unless result.sort == .type do throw "variance free alias has a non-type RHS"
  pure result

def query (definitions : Array DefinitionId) (identity : DefinitionIdentity) :
    Except String (Array Miri.MIR.Variance) :=
  VarianceInference.query (declaration definitions) (expandAlias definitions) 16384 identity

end Miri.Input.VarianceMaterial
