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
/-- Canonical source pattern identities; range constants share the program's
TypeConst table and Or children share this pattern table. -/
inductive PatternIdentity where
  | range (start finish : MIR.TypeConstId)
  | or (children : Array Nat)
  | notNull
  deriving Repr, DecidableEq

private partial def lowerPattern (ctx : LowerContext) (tables : CompilerTables)
    (nodes : Array PatternIdentity) (pattern : CompilerPattern) : Result (Nat × CompilerTables × Array PatternIdentity) := do
  let (value,tables,nodes) ← match pattern with
    | .range start finish => do
      unless start < tables.typeConstants.size && finish < tables.typeConstants.size do
        throw "compiler pattern constant ID out of bounds"
      pure (PatternIdentity.range start finish,tables,nodes)
    | .or children => do
      let mut tables := tables
      let mut nodes := nodes
      let mut ids := #[]
      for child in children do
        let (id,nextTables,nextNodes) ← lowerPattern ctx tables nodes child
        tables := nextTables; nodes := nextNodes; ids := ids.push id
      pure (PatternIdentity.or ids,tables,nodes)
    | .notNull => pure (PatternIdentity.notNull,tables,nodes)
  match nodes.toList.idxOf? value with
  | some id => pure (id,tables,nodes)
  | none => pure (nodes.size,tables,nodes.push value)

structure Prepared where
  context : CompilerFacts.Context
  patterns : Array PatternIdentity
  /-- Decoder-validated canonical type IDs equal row positions; both successful
  classifications and deferred errors retain that dense indexing. -/
  castTypes : Array (Result CastTypeInfo)
  obligations : Array Obligation

private def source (context : CompilerFacts.Context) (id : TypeId) : Result TypeNode :=
  (context.runtime.node id).mapError toString
private def castType (context : CompilerFacts.Context) (tables : CompilerTables)
    (patternIds : Array (TypeId × Nat)) (id : TypeId) : Result (CastTypeInfo × CompilerTables) := do
  let node ← source context id
  let unchanged value := pure (value,tables)
  match node.shape with
  | .int (.known kind) | .uint (.known kind) => unchanged (.integer kind)
  | .float kind =>
    let format ← match kind with
      | .f16 => pure FloatFormat.binary16 | .f32 => pure .binary32
      | .f64 => pure .binary64 | .f128 => pure .binary128
      | _ => throw "unsupported compiler float format"
    unchanged (.floating format)
  | .bool => unchanged .boolean | .char => unchanged .character
  | .rawPointer pointee _ => unchanged (.rawPointer pointee)
  | .reference pointee .. => unchanged (.reference pointee)
  | .functionPointer .. => unchanged .fnPointer
  | .adt data => unchanged (.adt data.definition)
  | .tuple elements => unchanged (.tuple elements)
  | .functionDefinition definition args .. => unchanged (.fnDefinition definition args)
  | .closure definition args count => unchanged (.closure definition args count)
  | .array element .. =>
    let layout ← CompilerFacts.layoutOf context id
    let .Array _ count := layout.layout.fields | throw "array compiler layout lacks source array count"
    unchanged (.array element count)
  | .slice element => unchanged (.slice element)
  | .dynamicTraitObject ids .. =>
    unchanged (.dynamic ids)
  | .patternType base _ =>
    let some (_,patternId) := patternIds.find? (·.1 == id) | throw "canonical compiler pattern identity missing"
    unchanged (.pattern base patternId)
  | _ => throw "type kind is outside the cast operand domain"

def prepare (context : CompilerFacts.Context) : Result Prepared := do
  let loweringContext := context.loweringContext
  let mut tables := context.program.compilerTables
  let mut casts := #[]
  let mut obligations := #[]
  let mut patterns := #[]
  let mut patternIds := #[]
  for node in context.runtime.source.types do
    if let some pattern := node.pattern then
      match lowerPattern loweringContext tables patterns pattern with
      | .ok (id,nextTables,nextPatterns) =>
        tables := nextTables; patterns := nextPatterns; patternIds := patternIds.push (node.id,id)
      | .error error => obligations := obligations.push ⟨s!"types[{node.id}].pattern",error⟩
  for node in context.runtime.source.types do
    match castType context tables patternIds node.id with
    | .ok (kind,next) => casts := casts.push (.ok kind); tables := next
    | .error error =>
      casts := casts.push (.error error)
      obligations := obligations.push ⟨s!"types[{node.id}].cast",error⟩
  pure ⟨context.withProgram (context.program.withCompilerTables tables),patterns,casts,obligations⟩

def castTypeInfo (prepared : Prepared) (id : TypeId) : Result CastTypeInfo := do
  let some result := prepared.castTypes[id]? | throw "compiler cast type identity missing"
  result
private def dynamicPredicates (prepared : Prepared) (id : TypeId) : Result PredicateList := do
  let .dynamicTraitObject ids .. := (← source prepared.context id).shape | throw "dynamic predicate query on non-dynamic type"
  pure ids

def validityKind (prepared : Prepared) (id : TypeId) : Result ValidityVisitor.TypeKind := do
  let context := prepared.context
  let node ← source context id
  match node.shape with
  | .bool => pure .boolean | .char => pure .character | .int _ | .uint _ => pure .integer
  | .float _ => pure .float | .functionPointer .. => pure .functionPointer | .never => pure .never
  | .foreign _ => pure .foreign | .functionDefinition .. => pure .functionDefinition
  | .rawPointer pointee _ => return .rawPointer pointee (← CompilerFacts.boolean context pointee "is_sized")
  | .reference _ mutable _ => pure (.reference (mutable == .Mut))
  | .str => pure .string
  | .array element .. | .slice element => pure (.sequence element)
  | .dynamicTraitObject .. => return .dynamic (← dynamicPredicates prepared id)
  | .patternType base _ => pure (.pattern base)
  | .unsafeBinder .. => pure .unsafeBinder
  | .adt _ | .tuple _ | .closure .. | .coroutine .. | .coroutineClosure .. =>
    if ← CompilerFacts.boolean context id "is_box" then pure .box else
      return .aggregate (← CompilerFacts.boolean context id "is_like_maybe_dangling")
        (← CompilerFacts.boolean context id "is_unsafe_cell") (node.shapeMetadata.adtKind == some .enumKind)
  | _ => throw "non-normalized/unsupported compiler type in validity query"

def metadataTail (prepared : Prepared) (id : TypeId) : Result ValidityVisitor.MetadataTail := do
  let tail ← CompilerFacts.requiredType prepared.context id "metadata_tail"
  let node ← source prepared.context tail
  match node.shapeKind with
  | .dynamicTraitObject => return .dynamic (← dynamicPredicates prepared tail)
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
