import Miri.Input.Model
import Miri.Input.RawFunctionSignature
import Miri.Input.TraitSelection.Match

/-! Ground Fn-family candidates from typed source callable signatures. This is
not an impl selector: no synthetic impl definition is constructed. ClosureKind
and the tupled RustCall signature are the actual ClosureArgs synthetics. FnPtr
compatibility is safe Rust ABI/nonvariadic; FnDef additionally needs raw target
feature attributes. Projection reduction returns a type plus real obligations. -/
namespace Miri.Input.SourceFnTraits
open GenericSubstitution TraitSelection
structure Source where
  definitions : Array DefinitionId
  traits : Program
  /-- Raw codegen_fn_attrs target_features. Missing material must error. -/
  fnDefinitionFeatures : DefinitionIdentity → Except String (Array String)
inductive Family where
  | closure | fnPointer | fnDefinition
  deriving Repr, DecidableEq
structure Result where
  family : Family
  output : Term
  obligations : Array Clause
  deriving Repr, DecidableEq
/-- Canonicalize serialization of validated raw FnSig JSON objects. All keys,
values, binders and physical identities remain part of the type relation. -/
def canonicalSignatureHeaders : Nat → Term → Except String Term
  | 0,_ => throw "fn builtin signature payload canonicalization exhausted"
  | fuel+1,term => do
    match term with
    | .binder variables (.node .aggregate "signature" payload children) =>
      let _ ← RawFunctionSignature.read term
      let payload ← Lean.Json.parse payload
      return .binder variables (.node .aggregate "signature" payload.compress
        (← children.mapM (canonicalSignatureHeaders fuel)))
    | .binder variables body => return .binder variables (← canonicalSignatureHeaders fuel body)
    | .node sort tag payload children => return .node sort tag payload (← children.mapM (canonicalSignatureHeaders fuel))
    | .definition sort tag identity children => return .definition sort tag identity (← children.mapM (canonicalSignatureHeaders fuel))
    | _ => pure term

private def definition (source : Source) (identity : DefinitionIdentity) : Except String DefinitionId := do
  let rows := source.definitions.filter (fun row => row.crateIndex==identity.crateIndex && row.index==identity.index)
  unless rows.size==1 do throw "fn builtin physical source definition absent or ambiguous"
  let some row := rows[0]? | throw "fn builtin source definition absent"
  pure row
private def rank : BuiltinTrait → Except String Nat
  | .fn => pure 0 | .fnMut => pure 1 | .fnOnce => pure 2
  | _ => throw "fn builtin requires a Fn-family declaration"
private def closureRank : Term → Except String Nat
  | .atom .type "int" "i8" => pure 0
  | .atom .type "int" "i16" => pure 1
  | .atom .type "int" "i32" => pure 2
  | _ => throw "fn builtin closure kind unresolved or malformed"
private def termArray : Terms → Array Term
  | .nil => #[] | .cons head tail => #[head] ++ termArray tail
private def tuple (term : Term) : Except String (Array Term) := do
  let .node .type "tuple" "" fields := term | throw "fn builtin Args is not a tuple"
  let fields := termArray fields
  unless fields.all (·.sort==.type) do throw "fn builtin tuple has a nontype field"
  pure fields
private def fnPointer (term : Term) : Except String RawFunctionSignature.Signature := do
  let .node .type "function_pointer" "" (.cons signature .nil) := term
    | throw "fn builtin callable signature is not a FnPtr"
  RawFunctionSignature.read signature
private def compatible (signature : RawFunctionSignature.Signature) : Bool :=
  signature.abi==.Rust && signature.safety==.Safe && !signature.cVariadic
private def signature (source : Source) (wanted fuel : Nat) (self : Term) :
    Except String (Option (Family × RawFunctionSignature.Signature)) := do
  match self with
  | .definition .type "closure" identity children =>
    let arguments := termArray children
    let owner ← definition source identity
    let some path := owner.rawPath | throw "fn builtin closure raw path absent"
    unless path.components.back?.any (·.kind=="closure") do throw "fn builtin owner is not a raw closure"
    let header ← DefinitionPath.requireGenerics path
    unless header.parameters.size==arguments.size && header.parentParameterCount+3==arguments.size do
      throw "fn builtin closure canonical synthetic scope mismatch"
    for (sort,argument) in header.parameters.zip arguments do
      unless sort==argument.sort do throw "fn builtin closure argument sort mismatch"
      Match.requireGround fuel argument
    let some kind := arguments[header.parentParameterCount]? | throw "fn builtin closure kind absent"
    let actual ← closureRank kind
    let some raw := arguments[header.parentParameterCount+1]? | throw "fn builtin closure signature absent"
    let signature ← fnPointer raw
    unless signature.abi==.RustCall && signature.safety==.Safe && !signature.cVariadic && signature.inputs.size==1 do
      throw "fn builtin closure synthetic signature header malformed"
    let some input := signature.inputs[0]? | throw "fn builtin closure tupled input absent"
    let _ ← tuple input
    let some captures := arguments[header.parentParameterCount+2]? | throw "fn builtin closure capture tuple absent"
    let _ ← tuple captures
    if actual>wanted then return none
    pure (some (.closure,signature))
  | .node .type "function_pointer" .. =>
    let signature ← fnPointer self
    pure (if compatible signature then some (.fnPointer,signature) else none)
  | .definition .type "function_definition" identity
      (.cons (.binder variables (.node .aggregate "arguments" "" children)) .nil) =>
    unless variables.isEmpty do throw "fn builtin FnDef generic binder requires universe relation"
    let arguments := termArray children
    let owner ← definition source identity
    let some header := owner.callableSource | throw "fn builtin FnDef callable source absent"
    unless header.definitionKind=="function" || header.definitionKind=="associated_function" do
      throw "fn builtin FnDef physical owner is not callable"
    let some template := owner.genericTemplate | throw "fn builtin FnDef raw signature template absent"
    let some scope := owner.sourceEnvironment | throw "fn builtin FnDef canonical source scope absent"
    unless scope.parent==scope.genericParent && template.parameters==scope.parameters do
      throw "fn builtin FnDef canonical source header mismatch"
    let .definition .type "function_definition" actual _ := template.typeExpression
      | throw "fn builtin FnDef source template malformed"
    unless actual==identity do throw "fn builtin FnDef physical template identity mismatch"
    template.checkArguments arguments
    let signature ← RawFunctionSignature.read (← template.instantiateSignature fuel arguments)
    if !compatible signature then return none
    let features ← source.fnDefinitionFeatures identity
    pure (if features.isEmpty then some (.fnDefinition,signature) else none)
  | .definition .type "coroutine_closure" .. =>
    throw "fn builtin coroutine closure requires async/coroutine source candidate provider"
  | .definition .type "function_definition" .. => throw "fn builtin FnDef source structure malformed"
  | _ => pure none

/-- Build a real builtin proof's nested obligations. Exact tuple relation is the
bounded ground slice of equate_trait_refs; higher-ranked relations stay errors.
FnPtr/FnDef candidates additionally prove Output:Sized, as pinned confirmation. -/
def query (source : Source) (normalize : Term → Except String Term) (fuel : Nat)
    (declaration : TraitDeclaration) (arguments : Array Term) : Except String (Option Result) := do
  let some kind := declaration.builtin | throw "fn builtin raw lang-item absent"
  let wanted ← rank kind
  let owner ← definition source declaration.definition
  let some scope := owner.sourceEnvironment | throw "fn builtin trait canonical source scope absent"
  unless scope.isTrait && scope.parameters==declaration.parameters && scope.parent==scope.genericParent &&
      !declaration.isAlias && !declaration.isAuto do
    throw "fn builtin trait canonical source header mismatch"
  unless declaration.parameters==#[.type,.type] && arguments.size==2 &&
      arguments.all (·.sort==.type) do throw "fn builtin requires canonical Self and Args tuple"
  if let some (GenericSubstitution.Term.definition .type "coroutine_closure" _ _) := arguments[0]? then
    throw "fn builtin coroutine closure requires async/coroutine source candidate provider"
  for argument in arguments do Match.requireGround fuel argument
  let some self := arguments[0]? | throw "fn builtin Self absent"
  let some actualArgs := arguments[1]? | throw "fn builtin Args absent"
  let _ ← tuple actualArgs
  let some (family,signature) ← signature source wanted fuel self | return none
  unless signature.variables.isEmpty do throw "fn builtin higher-ranked signature requires universe relation"
  let expectedArgs ← if family==.closure then
      match signature.inputs[0]? with | some value => pure value | none => throw "fn builtin tupled input absent"
    else pure (.node .type "tuple" "" (Terms.ofArray signature.inputs))
  let expectedArgs ← canonicalSignatureHeaders fuel (← normalize expectedArgs)
  let actualArgs ← canonicalSignatureHeaders fuel (← normalize actualArgs)
  if expectedArgs != actualArgs then return none
  let output ← canonicalSignatureHeaders fuel (← normalize signature.output)
  let obligations ← if family==.closure then pure #[] else do
    let rows := source.traits.traits.filter (·.builtin==some .sized)
    unless rows.size==1 do throw "fn builtin Output Sized source absent or ambiguous"
    let some sized := rows[0]? | throw "fn builtin Output Sized source absent"
    pure #[⟨#[],.trait ⟨.positive,⟨sized.definition,#[output]⟩⟩⟩]
  pure (some ⟨family,output,obligations⟩)

/-- Identify FnOnce::Output by its unique physical member and canonical source
scope. It is never an invented impl-associated value or a name-based lookup. -/
def outputProjection (source : Source) (normalize : Term → Except String Term) (fuel : Nat)
    (associated : DefinitionIdentity) (arguments : Array Term) : Except String (Option Result) := do
  let rows := source.traits.traits.filter (·.builtin==some .fnOnce)
  if rows.isEmpty then return none
  unless rows.size==1 do throw "fn builtin FnOnce source absent or ambiguous"
  let some fnOnce := rows[0]? | throw "fn builtin FnOnce source absent"
  let members := fnOnce.members.filter (·.kind=="type")
  unless members.size==1 do throw "fn builtin FnOnce Output source member absent or ambiguous"
  let some output := members[0]? | throw "fn builtin FnOnce Output member absent"
  if output.definition != associated then return none
  let traitOwner ← definition source fnOnce.definition
  let some traitScope := traitOwner.sourceEnvironment | throw "fn builtin FnOnce canonical source scope absent"
  unless traitScope.isTrait && traitScope.parameters==#[.type,.type] &&
      traitScope.parent==traitScope.genericParent do
    throw "fn builtin FnOnce canonical source header mismatch"
  let owner ← definition source associated
  let some scope := owner.sourceEnvironment | throw "fn builtin Output canonical source scope absent"
  let some parent := scope.genericParent | throw "fn builtin Output source parent absent"
  unless scope.parent==scope.genericParent && parent.definition==fnOnce.definition &&
      parent.parameterCount==2 && scope.parameters==#[.type,.type] do
    throw "fn builtin Output physical parent/header mismatch"
  let some alias := owner.aliasDeclaration | throw "fn builtin Output raw alias header absent"
  let .associated .trait aliasParent aliasCount _ := alias.kind
    | throw "fn builtin Output is not a trait associated alias"
  unless alias.definition==associated && aliasParent==fnOnce.definition && aliasCount==2 do
    throw "fn builtin Output physical alias owner mismatch"
  query source normalize fuel fnOnce arguments
end Miri.Input.SourceFnTraits
