import Miri.Input.CompilerWorldFacts
import Miri.Input.RuntimeArrayQueries
import Miri.Input.WorldTypeName
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
  if let some result := prepared.castTypes[id]? then return ← result
  unless id >= prepared.context.program.input.types.size do
    throw "compiler cast type identity missing"
  pure (← castType prepared.context prepared.context.program.compilerTables #[] id).1
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

private def worldLift [Monad m] [MonadExceptOf String m] (value : Except String A) : m A :=
  match value with | .ok result => pure result | .error error => throw error
private def worldConstructor (id : TypeId) : TypeArena.WorldM TypeArena.Constructor := do
  let world ← get
  match ← worldLift (world.lookupType id) with
  | .constructed value => pure value
  | .material source =>
    let some value ← worldLift (world.materialKey source) | throw "cast source constructor unavailable"
    pure value

/-- Pattern constants are checked in the current type/constant universe, never
against a freshly rebuilt compiler table. The returned syntax pool is explicit. -/
def lowerPatternInWorld : Nat → Array PatternIdentity → CompilerPattern →
    TypeArena.WorldM (Nat × Array PatternIdentity)
  | 0, _, _ => throw "world pattern lowering exhausted"
  | fuel + 1, nodes, pattern => do
    let (value,nodes) ← match pattern with
      | .range first last => do
        let world ← get
        let _ ← worldLift (world.lookupConstant first)
        let _ ← worldLift (world.lookupConstant last)
        pure (PatternIdentity.range first last,nodes)
      | .notNull => pure (PatternIdentity.notNull,nodes)
      | .or children => do
        let mut nodes := nodes
        let mut ids := #[]
        for child in children do
          let (id,next) ← lowerPatternInWorld fuel nodes child
          nodes := next; ids := ids.push id
        pure (PatternIdentity.or ids,nodes)
    match nodes.toList.idxOf? value with
    | some id => pure (id,nodes)
    | none => pure (nodes.size,nodes.push value)

def castTypeInfoInWorld (prepared : Prepared) (id : TypeId) : TypeArena.WorldM CastTypeInfo := do
  let world ← get
  let view ← worldLift (world.lookupType id)
  let kind ← worldLift (world.shapeKind id)
  if let .material source := view then
    match source.shape with
    | .functionPointer .. => return .fnPointer
    | .dynamicTraitObject ids .. => return .dynamic ids
    | .patternType base pattern =>
      let (patternId,nodes) ← lowerPatternInWorld (max 256 world.typeCount) prepared.patterns pattern
      unless nodes.size == prepared.patterns.size do
        throw "new runtime pattern syntax requires an execution-owned pattern pool"
      return .pattern base patternId
    | _ => pure ()
  match kind with
  | .bool => return .boolean | .char => return .character
  | _ => pure ()
  match ← worldConstructor id with
  | .integer _ integer => pure (.integer integer)
  | .float floating =>
    let format ← match floating with
      | .f16 => pure FloatFormat.binary16 | .f32 => pure .binary32
      | .f64 => pure .binary64 | .f128 => pure .binary128
      | _ => throw "unsupported world float format"
    pure (.floating format)
  | .rawPointer child _ => pure (.rawPointer child)
  | .reference child .. => pure (.reference child)
  | .adt identity _ => pure (.adt (← worldLift (world.definitionRef identity)))
  | .tuple children => pure (.tuple children)
  | .array child _ => pure (.array child (← RuntimeMetadata.arrayCountInWorld prepared.context.runtime id))
  | .slice child => pure (.slice child)
  | .functionDefinition identity args _ => pure (.fnDefinition (← worldLift (world.definitionRef identity)) args)
  | .closure identity args =>
    unless args.size >= 3 do throw "world closure synthetic arguments absent"
    let some (MIR.GenericArg.Type captures) := args.back? | throw "world closure capture tuple absent"
    let captures ← match ← worldLift (world.lookupType captures) with
      | .material source => match source.shape with
        | .tuple fields => pure fields.size | _ => throw "material closure captures are not a tuple"
      | .constructed (.tuple fields) => pure fields.size
      | _ => throw "constructed closure captures are not a tuple"
    pure (.closure (← worldLift (world.definitionRef identity)) args captures)
  | _ => throw "world constructor is outside the cast operand domain"

def validityKindInWorld (prepared : Prepared) (id : TypeId) : TypeArena.WorldM ValidityVisitor.TypeKind := do
  let context := prepared.context
  let world ← get
  let view ← worldLift (world.lookupType id)
  let kind ← worldLift (world.shapeKind id)
  match kind with
  | .bool => return .boolean | .char => return .character | .int | .uint => return .integer
  | .float => return .float | .functionPointer => return .functionPointer | .never => return .never
  | .foreign => return .foreign | .functionDefinition => return .functionDefinition | .str => return .string
  | .rawPointer =>
    let .rawPointer child _ ← worldConstructor id | throw "raw pointer world kind mismatch"
    return .rawPointer child (← CompilerFacts.booleanInWorld context child "is_sized")
  | .reference =>
    let .reference _ mutable _ ← worldConstructor id | throw "reference world kind mismatch"
    return .reference (mutable == .Mut)
  | .array =>
    let .array child _ ← worldConstructor id | throw "array world kind mismatch"
    return .sequence child
  | .slice =>
    let .slice child ← worldConstructor id | throw "slice world kind mismatch"
    return .sequence child
  | .dynamicTraitObject =>
    let .material source := view | throw "constructed dynamic predicates are not available"
    let .dynamicTraitObject predicates .. := source.shape | throw "dynamic world kind mismatch"
    return .dynamic predicates
  | .patternType =>
    let .material source := view | throw "constructed pattern source is not available"
    let .patternType child _ := source.shape | throw "pattern world kind mismatch"
    return .pattern child
  | .unsafeBinder => return .unsafeBinder
  | .adt | .tuple | .closure | .coroutine | .coroutineClosure =>
    if ← CompilerFacts.booleanInWorld context id "is_box" then return .box
    let enumKind ← if kind == .adt then do
      pure ((← RuntimeMetadata.adtDeclarationInWorld context.runtime id).kind == .enumKind)
      else pure false
    return .aggregate (← CompilerFacts.booleanInWorld context id "is_like_maybe_dangling")
      (← CompilerFacts.booleanInWorld context id "is_unsafe_cell") enumKind
  | _ => throw "world validity requires a normalized supported type"

def metadataTailInWorld (prepared : Prepared) (id : TypeId) : TypeArena.WorldM ValidityVisitor.MetadataTail := do
  let tail ← CompilerFacts.requiredTypeInWorld prepared.context id "metadata_tail"
  let world ← get
  match ← worldLift (world.lookupType tail) with
  | .material source => match source.shape with
    | .dynamicTraitObject ids .. => pure (.dynamic ids)
    | .str | .slice _ => pure .sliceOrStr | .foreign _ => pure .foreign
    | _ => throw "metadata validity tail is sized or unsupported"
  | .constructed value => match value with
    | .str | .slice _ => pure .sliceOrStr | .foreign _ => pure .foreign
    | _ => throw "constructed metadata validity tail is sized or unsupported"

def typeNameInWorld (prepared : Prepared) (id : TypeId) : TypeArena.WorldM String := do
  WorldTypeName.query prepared.context.runtime (max 256 (← get).typeCount) id

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
