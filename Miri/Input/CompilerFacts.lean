import Miri.Input.StructuralSized
import Miri.Input.StructuralNeedsDrop
import Miri.Input.StructuralAutoTraits
import Miri.Input.CompilerGlobals
import Miri.Input.CompilerPrimitiveFacts
import Miri.Input.StructuralNormalization
import Miri.Input.StructuralDeref
import Miri.Input.StructuralTail
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
  let ctx := match context.lowering with
    | some prepared => prepared
    | none => LowerContext.ofDocument context.program.input
  ctx.withLazyTypes context.program.input.types

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

private def normalize (context : Context) (id : TypeId) : Result TypeId :=
  StructuralNormalization.normalize (node context) context.program.input.types
    (id + context.program.input.types.size + 1) id

private def lazyBoolean (context : Context) (query : String) : Nat → TypeId → Result Bool
  | 0, _ => .error "lazy type boolean traversal exhausted"
  | fuel + 1, id => do
    let source ← node context id
    if id < context.program.input.types.size then
      if ["is_freeze", "is_unpin", "is_unsafe_unpin"].contains query then
        if ← StructuralAutoTraits.trivial (fun ty => return (← node context ty).shape) (fuel + 1) id then
          return true
      let f ← facts context id
      let some (_, result) := f.booleanQueries.find? (·.1 == query)
        | throw s!"missing material boolean query {query}"
      return result
    if ["is_box", "is_global_box", "is_unsafe_cell", "is_c_void", "is_simd"].contains query then return false
    match source.shape with
    | .rawPointer .. | .reference .. =>
      if query == "needs_drop" then return false
      if ["is_sized", "is_freeze", "is_unpin", "is_unsafe_unpin"].contains query then return true
    | .array child _ constructor =>
      if query == "is_sized" then
        let _ ← context.runtime.lookup id |>.mapError toString
        return true
      if query == "needs_drop" && constructor.count == 0 then return false
      if ["is_freeze", "is_unpin", "is_unsafe_unpin", "needs_drop"].contains query then
        return ← lazyBoolean context query fuel child
    | _ => pure ()
    throw s!"unimplemented lazy type boolean query {query}"

def boolean (context : Context) (id : TypeId) (query : String) : Result Bool := do
  -- Pinned rustc TyKind tests in compiler_facts_json: inspect the original
  -- shape before normalization. The input type language represents Alias but
  -- excludes Param/Bound/Placeholder/Infer/Error nodes.
  if query == "is_dynamic" then
    return (← node context id).shapeKind == .dynamicTraitObject
  if query == "is_too_generic" then
    return (← node context id).shapeKind == .alias
  if query == "is_sized" then
    if let some answer ← StructuralSized.query (fun ty => do
        pure (← node context (← normalize context ty)).shape)
        (id + context.program.input.types.size + 1) id then return answer
  if query == "needs_drop" then
    let normalizedShape (ty : TypeId) : Result TypeShape := do
      pure (← node context (← normalize context ty)).shape
    let adtMaterial (definition : DefinitionRef) : Result StructuralNeedsDrop.AdtMaterial := do
      let some raw := context.program.input.definitions[definition]?
        | throw "needs_drop ADT definition material absent"
      let some material := raw.adtDrop
        | throw "needs_drop raw ADT drop material absent"
      if let some destructor := material.destructor then
        unless destructor < context.program.input.definitions.size do
          throw "needs_drop destructor definition identity out of bounds"
      pure material
    if let some answer ← StructuralNeedsDrop.query normalizedShape adtMaterial
        (id + context.program.input.types.size + 1) id then return answer
  if id >= context.program.input.types.size then
    return ← lazyBoolean context query (id + context.program.input.types.size + 1) id
  let originalFacts ← facts context id
  if query == "is_freeze" || query == "is_unpin" || query == "is_unsafe_unpin" then
    let normalized ← if ← StructuralNormalization.identityReady context.program.input.types
        (context.program.input.types.size + 1) id then pure id else do
      let some (_, some target) := originalFacts.typeQueries.find? (·.1 == "normalized")
        | throw "missing auto-trait normalization dependency"
      pure target
    if ← StructuralAutoTraits.trivial (fun ty => return (← node context ty).shape)
        (context.program.input.types.size + 1) normalized then return true
  let facts := originalFacts
  let some (_,entry) := facts.booleanQueries.find? (·.1 == query) | throw s!"missing compiler boolean query {query}"
  pure entry

def optionalType (context : Context) (id : TypeId) (query : String) : Result (Option TypeId) := do
  let source ← node context id
  let entry ← if query == "normalized" then
      pure (some (← normalize context id))
    else if query == "metadata_tail" then do
      let root ← normalize context id
      let result ← StructuralTail.tail (fun ty => return (← node context ty).shape)
        (normalize context) (id + context.runtime.source.types.size + 1) root
      pure (some result)
    else if query == "builtin_deref_explicit" || query == "builtin_deref_implicit" || query == "boxed_type" then do
      -- Signature-bound source material keeps its Binder graph while facts
      -- use the explicitly instantiated query view recorded by the exporter.
      let source ← node context (source.layoutQueryInputTypeId.getD id)
      let isBox ← if source.shapeKind == .adt then do
        let f ← facts context id
        let some (_, isBox) := f.booleanQueries.find? (·.1 == "is_box")
          | throw "missing Box definition identity"
        pure isBox
      else pure false
      if query == "boxed_type" then StructuralDeref.boxedType source.shape isBox
      else StructuralDeref.builtinDeref source.shape isBox (query == "builtin_deref_explicit")
    else if query == "pointer_metadata_type" then
      pure (some (← context.runtime.pointerMetadataType id |>.mapError toString))
    else if id >= context.program.input.types.size && query == "unsafe_binder_erased" then
      pure none
    else do
      let f ← facts context id
      let some (_, entry) := f.typeQueries.find? (·.1 == query)
        | throw s!"missing compiler type query {query}"
      pure entry
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
