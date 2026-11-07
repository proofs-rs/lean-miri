import Miri.Input.RuntimeProgram
import Miri.Input.CompilerGlobals
import Miri.Input.CallCompatibility
import Miri.Input.CompilerPrimitiveFacts
import Miri.Interpreter.TypedRetag
import Miri.Interpreter.LayoutCompat
import Miri.Interpreter.ValidityVisitor

/-! Required compiler facts for the fixed interpreter. Query evidence is keyed
by exact compilation-local TyId and explicit fully_monomorphized typing_env.
Sources: rustc_middle ty/{util,sty,inhabitedness}; interpret/{call,visitor,validity}
and Miri helpers.rs UnsafeCellVisitor/tree_borrows/mod.rs NewPermission.
No diagnostic type spelling establishes a semantic property. -/
namespace Miri.Input.CompilerFacts
open Lean Miri.ABI Miri.Memory Miri.Interpreter
abbrev Result := Except String
private def require (value : Option A) (message : String) : Result A :=
  match value with | some value => .ok value | none => .error message

private def computeUnitLayout (runtime : RuntimeMetadata.Indexed) :
    Result (TyAndLayout TypeId) := do
  let mut found := none
  for source in runtime.source.types do
    if source.shapeKind == .tuple then
      let elements ← RuntimeMetadata.typeElements runtime source.id |>.mapError toString
      if elements.isEmpty then
        if found.isSome then throw "ambiguous compiler unit type identity"
        found := some source.id
  let some id := found | throw "compiler unit type identity missing"
  runtime.lookup id |>.mapError toString

set_option autoImplicit false in
structure UnitLayoutCache (runtime : RuntimeMetadata.Indexed) where
  private mk ::
  value : Result (TyAndLayout TypeId)
  exact : value = computeUnitLayout runtime

def bindUnitLayout (runtime : RuntimeMetadata.Indexed) : UnitLayoutCache runtime :=
  let value := computeUnitLayout runtime
  ⟨value, rfl⟩

structure Context where
  owner : RuntimeProgram
  unitLayoutCache : Option (UnitLayoutCache (RuntimeMetadata.Indexed.ofMetadata owner.runtime)) := none

@[inline] def Context.program (context : Context) : LoweredProgram := context.owner.program
@[inline] def Context.runtime (context : Context) : RuntimeMetadata.Indexed :=
  RuntimeMetadata.Indexed.ofMetadata context.owner.runtime

def Context.primitiveLayout (context : Context) (key : String) :
    Except String (TyAndLayout TypeId) :=
  CompilerPrimitiveFacts.primitiveLayout context.runtime.toRuntimeMetadata key

def Context.orderingLayout (context : Context) : Except String (TyAndLayout TypeId) :=
  CompilerPrimitiveFacts.orderingLayout context.runtime.toRuntimeMetadata

/-- Compiler preparation replaces lowered tables, keeping one input owner. -/
def Context.withProgram (context : Context) (program : LoweredProgram) : Context :=
  {context with owner := context.owner.withProgram program}

def ofOwner (owner : RuntimeProgram) : Context := Id.run do
  let indexed := RuntimeMetadata.Indexed.ofMetadata owner.runtime
  return {
    owner := owner
    unitLayoutCache := some (bindUnitLayout indexed)}

def ofProgram (program : LoweredProgram) : Result Context := do
  return ofOwner (← RuntimeProgram.ofProgram program)
private def node (context : Context) (id : TypeId) : Result TypeNode :=
  (context.runtime.node id).mapError toString
private def facts (context : Context) (id : TypeId) : Result TypeCompilerFacts := do
  let source ← node context id
  let some facts := source.compilerFacts | throw s!"missing compiler_facts for type {id}"
  unless facts.inputTypeId == id && facts.typingEnvironment == "fully_monomorphized" do
    throw "compiler query type/typing-environment key mismatch"
  pure facts

def booleanRuntime (runtime : RuntimeMetadata) (id : TypeId) (query : String) : Result Bool := do
  let source ← runtime.node id |>.mapError toString
  let some facts := source.compilerFacts | throw s!"missing compiler_facts for type {id}"
  unless facts.inputTypeId == id && facts.typingEnvironment == "fully_monomorphized" do
    throw "compiler query type/typing-environment key mismatch"
  let tables := runtime.source.compilerFactTables
  let entries ← tables.booleanQueries.lookup facts.booleanQueries |>.mapError (fun id => s!"invalid boolean query map {id}")
  let some (_,id) := entries.find? (·.1 == query) | throw s!"missing compiler boolean query {query}"
  let entry ← tables.booleanValues.lookup id |>.mapError (fun id => s!"invalid boolean query {id}")
  unless entry.status == .supported do throw s!"unresolved compiler query {query}: {entry.reason}"
  let some value := entry.value | throw s!"compiler boolean query {query} has no value"
  pure value


def boolean (context : Context) (id : TypeId) (query : String) : Result Bool :=
  booleanRuntime context.owner.runtime id query

def optionalType (context : Context) (id : TypeId) (query : String) : Result (Option TypeId) := do
  let facts ← facts context id
  let tables := context.runtime.source.compilerFactTables
  let entries ← tables.typeQueries.lookup facts.typeQueries |>.mapError (fun id => s!"invalid type query map {id}")
  let some (_,id) := entries.find? (·.1 == query) | throw s!"missing compiler type query {query}"
  let entry ← tables.typeValues.lookup id |>.mapError (fun id => s!"invalid type query {id}")
  unless entry.status == .supported do throw s!"unresolved compiler type query {query}: {entry.reason}"
  if let some ty := entry.value then let _ ← node context ty
  pure entry.value

def requiredType (context : Context) (id : TypeId) (query : String) : Result TypeId := do
  let some ty ← optionalType context id query | throw s!"compiler query {query} returned None"
  pure ty

def layoutOf (context : Context) (id : TypeId) : Result (TyAndLayout TypeId) :=
  (context.runtime.lookup id).mapError toString

def unitLayout (context : Context) : Result (TyAndLayout TypeId) := do
  match context.unitLayoutCache with
  | some cached => cached.value
  | none => computeUnitLayout context.runtime

def builtinDeref (context : Context) (id : TypeId) (explicit : Bool) : Result (Option TypeId) :=
  optionalType context id (if explicit then "builtin_deref_explicit" else "builtin_deref_implicit")

def referencePointee (context : Context) (id : TypeId) : Result (TypeId × MIR.Mutability) := do
  let source ← node context id
  unless source.shapeKind == .reference do throw "reference_pointee requested for a non-reference"
  let some pointee := source.relations.pointee | throw "reference pointee absent"
  let _ ← node context pointee
  let some mutable := source.relations.mutable | throw "reference mutability absent"
  pure (pointee,if mutable then .Mut else .Not)

def retagTypeShape (context : Context) (id : TypeId) : Result Miri.TreeBorrows.RetagPipeline.RetagTypeShape := do
  let source ← node context id
  pure ⟨← boolean context id "is_global_box",source.shapeKind == .reference,
    source.shapeKind == .rawPointer,← boolean context id "is_box"⟩

private def adtFacts (context : Context) (id : TypeId) : Result CompilerAdtFacts := do
  let some value := (← facts context id).adt | throw "ADT query requested for a non-ADT"
  return value

def itemName (context : Context) (id : TypeId) : Result String := do
  return (← adtFacts context id).itemName

def nonnullOptimizationGuaranteed (context : Context) (id : TypeId) : Result Bool := do
  return (← adtFacts context id).nonnullOptimizationGuaranteed

def reprEqualUpToSeed (context : Context) (left right : TypeId) : Result Bool := do
  let a ← RuntimeMetadata.typeRepresentation context.runtime left |>.mapError toString
  let b ← RuntimeMetadata.typeRepresentation context.runtime right |>.mapError toString
  return a.integer == b.integer && a.alignBytes == b.alignBytes && a.packBytes == b.packBytes &&
    a.flagsBits == b.flagsBits && a.scalableElement == b.scalableElement

def adtInfo (context : Context) (id : TypeId) : Result (LayoutCompat.AdtInfo TypeId) :=
  CallCompatibility.adt context.runtime id |>.mapError toString

def compatibilityKind (context : Context) (id : TypeId) : Result (LayoutCompat.TypeKind TypeId) := do
  let source ← node context id
  match source.shapeKind with
  | .tuple => pure .tuple | .never => pure .never | .functionDefinition => pure .functionDefinition
  | .closure => pure .closure | .coroutine => pure .coroutine | .coroutineClosure => pure .coroutineClosure
  | .array => return .array (← require source.relations.element "array element absent")
  | .adt => pure .adt
  | .patternType => return .pattern (← require source.relations.base "pattern base absent")
  | .unsafeBinder => pure .unsafeBinder | .alias => pure .alias
  | .reference => return .reference (← require source.relations.pointee "pointee type absent")
  | .rawPointer => return .rawPointer (← require source.relations.pointee "pointee type absent")
  | .functionPointer => pure .functionPointer
  | .int | .uint =>
    match source.shapeMetadata.signedKind <|> source.shapeMetadata.unsignedKind with
    | some (.known kind) => pure (.integer kind)
    | _ => throw "compiler integer kind missing"
  | .char => pure .char
  | .bool | .float | .foreign | .str | .slice | .dynamicTraitObject => pure .other
  | _ => throw "non-normalized compiler type in ABI compatibility query"

private def lift (value : Result A) : EStateM StepError S A :=
  match value with | .ok value => pure value | .error error => throw (.invalidProgram error)

/-- Replace only compiler leaves; all actual memory/projection/dyn operations
retain their source implementation and stateful failure behavior. -/
def typedRetagHooks (context : Context) (machine : TypedRetag.Hooks K U) : TypedRetag.Hooks K U :=
  { machine with
    typeShape := fun ty => lift (retagTypeShape context ty)
    builtinDeref := fun ty => lift (requiredType context ty "builtin_deref_explicit")
    referencePointee := fun ty => lift (referencePointee context ty)
    isUnpin := fun ty => lift (boolean context ty "is_unpin")
    isUnsafeUnpin := fun ty => lift (boolean context ty "is_unsafe_unpin")
    typeIsFreeze := fun ty => lift (boolean context ty "is_freeze")
    freeze := { machine.freeze with
      isUnsafeCell := fun ty => lift (boolean context ty "is_unsafe_cell")
      typeIsFreeze := fun ty => lift (boolean context ty "is_freeze")
      isDynamic := fun ty => lift (boolean context ty "is_dynamic")
      isBox := fun ty => lift (boolean context ty "is_box")
      isTooGeneric := fun ty => lift (boolean context ty "is_too_generic") } }

def compatibilityQueries (context : Context) : LayoutCompat.Queries TypeId S := {
  target := context.runtime.target
  kind := fun ty => lift (compatibilityKind context ty)
  adt := fun ty => lift (adtInfo context ty)
  field := fun layout index => lift ((context.runtime.field layout index).mapError toString)
  layoutOf := fun ty => lift (layoutOf context ty)
  unitLayout := lift (unitLayout context)
  eraseUnsafeBinder := fun ty => lift (requiredType context ty "unsafe_binder_erased")
  normalize := fun ty => lift (requiredType context ty "normalized")
  reprEqualUpToSeed := fun a b => lift (reprEqualUpToSeed context a b)
  itemName := fun ty => lift (itemName context ty)
  nonnullOptimizationGuaranteed := fun ty => lift (nonnullOptimizationGuaranteed context ty)
  isGlobalBox := fun ty => lift (boolean context ty "is_global_box")
  boxedType := fun ty => lift (requiredType context ty "boxed_type")
  pointerMetadataType := fun ty => lift (requiredType context ty "pointer_metadata_type") }

end Miri.Input.CompilerFacts
