import Miri.Input.CompilerFacts
import Miri.Interpreter.Cast

/-! Compiler shape/query adapters for Cast and ValidityVisitor. Definition and
TypeConst IDs are appended to the existing shared bundle, never source indices.
Dynamic-predicate tokens index an explicit shared table of original compiler
predicate arrays; vtable consumers must use this same table and still discharge
normalization/stable-comparison queries. -/
namespace Miri.Input.CompilerFactAdapters
open Lean Miri.ABI Miri.Memory Miri.Interpreter
abbrev Result := Except String
structure Prepared where
  context : CompilerFacts.Context
  dynamicPredicates : MIR.SharedTable PredicateListData
  castTypes : Array (TypeId × Result CastTypeInfo)
  obligations : Array Obligation

private def field (j : Json) (key : String) : Result Json := j.getObjVal? key
private def source (context : CompilerFacts.Context) (id : TypeId) : Result TypeNode :=
  (context.runtime.node id).mapError toString
private def sourceDefinition (node : TypeNode) : Result DefinitionId := do
  let some facts := node.compilerFacts | throw "type compiler definition evidence missing"
  let some value := facts.definition | throw "compiler definition absent"
  pure value
private def ensureDefinition (tables : CompilerTables) (id : DefinitionId) : CompilerTables :=
  if tables.definitions.contains id then tables else { tables with definitions := tables.definitions.push id }

private def castType (context : CompilerFacts.Context) (tables : CompilerTables) (predicates : MIR.SharedTable PredicateListData)
    (patternIds : Array (Option Nat)) (id : TypeId) : Result (CastTypeInfo × CompilerTables) := do
  let node ← source context id
  let child (value : Option TypeId) := do
    let some id := value | throw "compiler child type absent"
    let _ ← source context id
    pure id
  let unchanged value := pure (value,tables)
  match node.shapeKind with
  | .int | .uint =>
    match node.shapeMetadata.signedKind <|> node.shapeMetadata.unsignedKind with
    | some (.known kind) => unchanged (.integer kind)
    | _ => throw "integer kind evidence unavailable"
  | .float =>
    let format ← match node.shapeMetadata.floatKind with
      | some .f16 => pure FloatFormat.binary16 | some .f32 => pure .binary32
      | some .f64 => pure .binary64 | some .f128 => pure .binary128
      | _ => throw "unsupported compiler float format"
    unchanged (.floating format)
  | .bool => unchanged .boolean | .char => unchanged .character
  | .rawPointer => unchanged (.rawPointer (← child node.relations.pointee))
  | .reference => unchanged (.reference (← child node.relations.pointee))
  | .functionPointer => unchanged .fnPointer
  | .adt =>
    let definition ← sourceDefinition node
    let tables := ensureDefinition tables definition
    pure (.adt (← lookupDefinitionId tables.definitions definition),tables)
  | .functionDefinition | .closure =>
    let value ← context.runtime.source.mirTables.functionType id
    if node.shapeKind == .functionDefinition then unchanged (.fnDefinition value.definition value.args)
    else
      let some count := node.relations.upvarCount | throw "closure upvar count absent"
      unchanged (.closure value.definition value.args count)
  | .array =>
    let layout ← CompilerFacts.layoutOf context id
    let .Array _ count := layout.layout.fields | throw "array compiler layout lacks source array count"
    unchanged (.array (← child node.relations.element) count)
  | .slice => unchanged (.slice (← child node.relations.element))
  | .dynamicTraitObject =>
    let some token := node.relations.predicates | throw "dynamic predicate list absent"
    let _ ← predicates.lookup token |>.mapError (fun id => s!"invalid predicate list {id}")
    unchanged (.dynamic token)
  | .patternType =>
    let some (some token) := patternIds[id]? | throw "canonical compiler pattern identity missing"
    let some _ := context.runtime.source.mirTables.patterns[token]? | throw "invalid canonical compiler pattern ID"
    unchanged (.pattern (← child node.relations.base) token)
  | _ => throw "type kind is outside the cast operand domain"

def prepare (context : CompilerFacts.Context) : Result Prepared := do
  let predicates := context.program.input.vtableTables.predicateLists
  let mut tables := context.program.compilerTables
  let mut casts := #[]
  let mut obligations := #[]
  let patternIds := context.program.input.mirTables.patternIds
  for node in context.runtime.source.types do
    match castType context tables predicates patternIds node.id with
    | .ok (kind,next) => casts := casts.push (node.id,.ok kind); tables := next
    | .error error =>
      casts := casts.push (node.id,.error error)
      obligations := obligations.push ⟨s!"types[{node.id}].cast",error⟩
  pure ⟨context.withProgram (context.program.withCompilerTables tables),predicates,casts,obligations⟩

def castTypeInfo (prepared : Prepared) (id : TypeId) : Result CastTypeInfo := do
  let some (_,result) := prepared.castTypes.find? (·.1 == id) | throw "compiler cast type identity missing"
  result
private def dynamicToken (prepared : Prepared) (id : TypeId) : Result Nat := do
  let node ← source prepared.context id
  let some token := node.relations.predicates | throw "dynamic predicate list absent"
  let _ ← prepared.dynamicPredicates.lookup token |>.mapError (fun id => s!"invalid predicate list {id}")
  pure token

def validityKind (prepared : Prepared) (id : TypeId) : Result ValidityVisitor.TypeKind := do
  let context := prepared.context
  let node ← source context id
  let child (value : Option TypeId) := do
    let some id := value | throw "compiler child type absent"
    let _ ← source context id
    pure id
  match node.shapeKind with
  | .bool => pure .boolean | .char => pure .character | .int | .uint => pure .integer
  | .float => pure .float | .functionPointer => pure .functionPointer | .never => pure .never
  | .foreign => pure .foreign | .functionDefinition => pure .functionDefinition
  | .rawPointer =>
    let pointee ← child node.relations.pointee
    return .rawPointer pointee (← CompilerFacts.boolean context pointee "is_sized")
  | .reference => return .reference ((← CompilerFacts.referencePointee context id).2 == .Mut)
  | .str => pure .string
  | .array | .slice => return .sequence (← child node.relations.element)
  | .dynamicTraitObject => return .dynamic (← dynamicToken prepared id)
  | .patternType => return .pattern (← child node.relations.base)
  | .unsafeBinder => pure .unsafeBinder
  | .adt | .tuple | .closure | .coroutine | .coroutineClosure =>
    if ← CompilerFacts.boolean context id "is_box" then pure .box else
      return .aggregate (← CompilerFacts.boolean context id "is_like_maybe_dangling")
        (← CompilerFacts.boolean context id "is_unsafe_cell") (node.shapeMetadata.adtKind == some .enumKind)
  | _ => throw "non-normalized/unsupported compiler type in validity query"

def metadataTail (prepared : Prepared) (id : TypeId) : Result ValidityVisitor.MetadataTail := do
  let tail ← CompilerFacts.requiredType prepared.context id "metadata_tail"
  let node ← source prepared.context tail
  match node.shapeKind with
  | .dynamicTraitObject => return .dynamic (← dynamicToken prepared tail)
  | .slice | .str => pure .sliceOrStr
  | .foreign => pure .foreign
  | _ => throw "metadata validation requested for a sized or unsupported tail"

private def lift (value : Result A) : EStateM StepError S A :=
  match value with | .ok value => pure value | .error error => throw (.invalidProgram error)

def castHooks (prepared : Prepared) (machine : CastHooks P S C V) : CastHooks P S C V :=
  { machine with
    typeInfo := fun _ ty => lift (castTypeInfo prepared ty)
    layoutOf := fun _ ty => lift (CompilerFacts.layoutOf prepared.context ty)
    builtinDeref := fun _ ty explicit => lift (CompilerFacts.builtinDeref prepared.context ty explicit)
    ensureMonomorphic := fun _ ty => do
      unless ← lift (CompilerFacts.boolean prepared.context ty "is_monomorphic_enough") do throw (.invalidProgram "compiler type still requires instantiation") }

def validityHooks (prepared : Prepared) (machine : ValidityVisitor.Hooks P S C E Fn Abi Pad) : ValidityVisitor.Hooks P S C E Fn Abi Pad :=
  { machine with
    classify := fun _ ty => lift (validityKind prepared ty)
    metadataTail := fun _ ty => lift (metadataTail prepared ty)
    unitLayout := fun _ => lift (CompilerFacts.unitLayout prepared.context)
    typeName := fun _ ty => do pure (← lift (source prepared.context ty)).display
    opsemInhabited := fun _ ty => lift (CompilerFacts.boolean prepared.context ty "opsem_inhabited")
    isFreeze := fun _ ty => lift (CompilerFacts.boolean prepared.context ty "is_freeze") }
/-- The diagnostic type name is a pure compiler-node projection. -/
theorem validity_typeName_of_node (prepared : Prepared)
    (machine : ValidityVisitor.Hooks P S C E Fn Abi Pad) (choice : C)
    (ty : TypeId) (node : TypeNode)
    (found : prepared.context.runtime.node ty = .ok node) :
    (validityHooks prepared machine).typeName choice ty = pure node.display := by
  funext state
  simp [validityHooks, source, lift, found, Except.mapError,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]

end Miri.Input.CompilerFactAdapters
