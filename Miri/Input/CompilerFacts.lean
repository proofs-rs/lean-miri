import Miri.Input.CompilerGlobals
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

private def computeUnitLayout (runtime : RuntimeMetadata) :
    Result (TyAndLayout TypeId) := do
  let some source := runtime.source.types.find? (fun ty =>
    match ty.shape with | .tuple elements => elements.isEmpty | _ => false)
    | throw "compiler unit type identity missing"
  runtime.lookup source.id |>.mapError toString

structure Context where
  runtime : RuntimeMetadata
  program : LoweredProgram
  lowering : Option LowerContext := none

def Context.loweringContext (context : Context) : LowerContext :=
  match context.lowering with
  | some prepared => prepared
  | none => LowerContext.ofDocument context.program.input

def Context.primitiveLayout (context : Context) (key : String) :
    Except String (TyAndLayout TypeId) :=
  CompilerPrimitiveFacts.primitiveLayout context.runtime key

def Context.orderingLayout (context : Context) : Except String (TyAndLayout TypeId) :=
  CompilerPrimitiveFacts.orderingLayout context.runtime

/-- Prepare lowering metadata for the current program. -/
def Context.withProgram (context : Context) (program : LoweredProgram) : Context :=
  { context with program, lowering := some (LowerContext.ofDocument program.input) }

def ofProgram (runtime : RuntimeMetadata) (program : LoweredProgram) : Result Context := do
  let program := CompilerGlobals.prepareProgram program
  return {
    runtime
    program
    lowering := some (LowerContext.ofDocument program.input)
  }
private def node (context : Context) (id : TypeId) : Result TypeNode :=
  (context.runtime.node id).mapError toString
private def facts (context : Context) (id : TypeId) : Result TypeCompilerFacts := do
  let source ← node context id
  let some facts := source.compilerFacts | throw s!"missing compiler_facts for type {id}"
  unless facts.typingEnvironment == "fully_monomorphized" do
    throw "compiler query typing-environment mismatch"
  pure facts

def boolean (context : Context) (id : TypeId) (query : String) : Result Bool := do
  let facts ← facts context id
  let some (_,entry) := facts.booleanQueries.find? (·.1 == query) | throw s!"missing compiler boolean query {query}"
  pure entry

def optionalType (context : Context) (id : TypeId) (query : String) : Result (Option TypeId) := do
  let facts ← facts context id
  let some (_,entry) := facts.typeQueries.find? (·.1 == query) | throw s!"missing compiler type query {query}"
  if let some ty := entry then let _ ← node context ty
  pure entry

def requiredType (context : Context) (id : TypeId) (query : String) : Result TypeId := do
  let some ty ← optionalType context id query | throw s!"compiler query {query} returned None"
  pure ty
def layoutOf (context : Context) (id : TypeId) : Result (TyAndLayout TypeId) :=
  (context.runtime.lookup id).mapError toString

def unitLayout (context : Context) : Result (TyAndLayout TypeId) :=
  computeUnitLayout context.runtime

def builtinDeref (context : Context) (id : TypeId) (explicit : Bool) : Result (Option TypeId) :=
  optionalType context id (if explicit then "builtin_deref_explicit" else "builtin_deref_implicit")

def referencePointee (context : Context) (id : TypeId) : Result (TypeId × MIR.Mutability) := do
  let source ← node context id
  let .reference pointee mutability _ := source.shape
    | throw "reference_pointee requested for a non-reference"
  let _ ← node context pointee
  pure (pointee,mutability)

def retagTypeShape (context : Context) (id : TypeId) : Result Miri.TreeBorrows.RetagPipeline.RetagTypeShape := do
  let source ← node context id
  pure ⟨← boolean context id "is_global_box",source.shapeKind == .reference,
    source.shapeKind == .rawPointer,← boolean context id "is_box"⟩

private def adtFacts (context : Context) (id : TypeId) : Result AdtCompilerFacts := do
  let some value := (← facts context id).adt | throw "ADT query requested for a non-ADT"
  pure value

private def adtShape (context : Context) (id : TypeId) : Result AdtShape := do
  let .adt value := (← node context id).shape | throw "ADT layout query on non-ADT"
  pure value

def itemName (context : Context) (id : TypeId) : Result String :=
  return (← adtFacts context id).itemName

def nonnullOptimizationGuaranteed (context : Context) (id : TypeId) : Result Bool :=
  return (← adtFacts context id).nonnullOptimizationGuaranteed

def reprEqualUpToSeed (context : Context) (left right : TypeId) : Result Bool := do
  let a := (← adtShape context left).representation
  let b := (← adtShape context right).representation
  pure (a.integer == b.integer && a.alignBytes == b.alignBytes &&
    a.packBytes == b.packBytes && a.flagsBits == b.flagsBits && a.scalableElement == b.scalableElement)

def adtInfo (context : Context) (id : TypeId) : Result (LayoutCompat.AdtInfo TypeId) := do
  let data ← adtShape context id
  let kind := match data.kind with
    | .structKind => LayoutCompat.AdtKind.Struct | .unionKind => .Union | .enumKind => .Enum
  let variants := data.variants.map fun variant => variant.fields.map fun field =>
    ({ name := field.name, ty := field.typeId } : LayoutCompat.Field TypeId)
  pure ⟨kind,data.representation.transparent,data.representation.c,data.representation.rust,variants⟩

def compatibilityKind (context : Context) (id : TypeId) : Result (LayoutCompat.TypeKind TypeId) := do
  match (← node context id).shape with
  | .tuple _ => pure .tuple | .never => pure .never | .functionDefinition .. => pure .functionDefinition
  | .closure .. => pure .closure | .coroutine .. => pure .coroutine | .coroutineClosure .. => pure .coroutineClosure
  | .array element .. => pure (.array element)
  | .adt _ => pure .adt
  | .patternType base _ => pure (.pattern base)
  | .unsafeBinder .. => pure .unsafeBinder | .alias .. => pure .alias
  | .reference pointee .. => pure (.reference pointee)
  | .rawPointer pointee _ => pure (.rawPointer pointee)
  | .functionPointer .. => pure .functionPointer
  | .int (.known kind) | .uint (.known kind) => pure (.integer kind)
  | .char => pure .char
  | .bool | .float _ | .foreign _ | .str | .slice _ | .dynamicTraitObject .. => pure .other

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
