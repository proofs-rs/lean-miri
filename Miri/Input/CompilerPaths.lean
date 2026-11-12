import Miri.Input.CompilerFactAdapters

/-! Pinned interpret/validity.rs::aggregate_field_path_elem (371-452) and
visit_variant (1277-1290). Paths are diagnostics only. Field names come from
actual compiler definitions; dyn paths require the actual projected child type.
Captured-variable numeric names are used only after explicit capture-name query
evidence reports no binding name, as in the source fallback. -/
namespace Miri.Input.CompilerPaths
open Lean Miri.ABI Miri.Memory Miri.Interpreter
abbrev Result := Except String
private def node (context : CompilerFacts.Context) (id : TypeId) : Result TypeNode :=
  (context.runtime.node id).mapError toString
private def sourceVariant (source : TypeNode) (index : Nat) : Result AdtVariant := do
  let .adt data := source.shape | throw "compiler variant query requires ADT"
  let some variant := data.variants.find? (·.index == index) | throw "compiler variant identity missing"
  pure variant

def variantPath (context : CompilerFacts.Context) (layout : TyAndLayout TypeId) (index : Nat) : Result PathElem := do
  let source ← node context layout.ty
  match source.shapeKind with
  | .adt => return .variant (← sourceVariant source index).name
  | .coroutine => pure (.coroutineState index)
  | _ => throw "source invariant: variant path requested for non-variant type"

def fieldPath (context : CompilerFacts.Context) (layout : TyAndLayout TypeId)
    (index : Nat) (childType : TypeId) : Result PathElem := do
  let source ← node context layout.ty
  if let .Multiple _ _ tagField _ := layout.layout.variants then
    if tagField == index then
      if source.shapeMetadata.adtKind == some .enumKind then return .enumTag
      if source.shapeKind == .coroutine then return .coroutineTag
      throw "source invariant: tag path on non-variant type"
  match source.shapeKind with
  | .closure | .coroutine | .coroutineClosure =>
    let some facts := source.compilerFacts | throw "capture-name compiler evidence missing"
    let some names := facts.captureNames | throw "capture-name compiler array evidence missing"
    let name := match names[index]? with
      | none | some none => toString index
      | some (some name) => name
    pure (.capturedVar name)
  | .tuple => pure (.tupleElem index)
  | .adt =>
    let variantIndex ← match layout.layout.variants with
      | .Single index => pure index
      | .Empty => throw "source invariant: field path in Variants::Empty"
      | .Multiple .. => throw "source invariant: non-tag field path before variant selection"
    let fields := (← sourceVariant source variantIndex).fields
    let some item := fields.find? (·.index == index) | throw "compiler ADT field identity missing"
    return .field item.name
  | .array | .slice => pure (.arrayElem index)
  | .dynamicTraitObject =>
    unless index == 0 do throw "source invariant: dyn projected field index is not zero"
    return .dynDowncast (← node context childType).display
  | _ => throw "source invariant: aggregate field path on non-aggregate type"

private def worldLift [Monad m] [MonadExceptOf String m] (value : Except String A) : m A :=
  match value with | .ok result => pure result | .error error => throw error

def fieldPathInWorld (context : CompilerFacts.Context) (layout : TyAndLayout TypeId)
    (index : Nat) (child : TypeId) : TypeArena.WorldM PathElem := do
  let world ← get
  let kind ← worldLift (world.shapeKind layout.ty)
  if let .Multiple _ _ tagField _ := layout.layout.variants then
    if tagField == index then
      if kind == .coroutine then return .coroutineTag
      if kind == .adt && (← RuntimeMetadata.adtDeclarationInWorld context.runtime layout.ty).kind == .enumKind then
        return .enumTag
      throw "tag path requested for a non-variant world type"
  if kind == .array || kind == .slice then return .arrayElem index
  if kind == .tuple then return .tupleElem index
  if kind == .adt then
    let declaration ← RuntimeMetadata.adtDeclarationInWorld context.runtime layout.ty
    let variant ← match layout.layout.variants with
      | .Single variant => pure variant
      | .Empty => throw "field path in empty world layout"
      | .Multiple .. => throw "non-tag world field path requires variant selection"
    let some field := declaration.fields.find? (fun field =>
        field.variantIndex == variant && field.fieldIndex == index)
      | throw "canonical raw field name absent for world projection"
    return .field field.fieldName
  if kind == .dynamicTraitObject then
    unless index == 0 do throw "dynamic downcast path index is not zero"
    let .material source ← worldLift (world.lookupType child)
      | throw "constructed dynamic child name requires the source type printer"
    return .dynDowncast source.display
  match ← worldLift (world.lookupType layout.ty) with
  | .material _ => worldLift (fieldPath context layout index child)
  | .constructed _ => throw "constructed aggregate path requires canonical raw field names"

def variantPathInWorld (context : CompilerFacts.Context) (layout : TyAndLayout TypeId)
    (index : Nat) : TypeArena.WorldM PathElem := do
  let world ← get
  if (← worldLift (world.shapeKind layout.ty)) == .coroutine then return .coroutineState index
  unless (← worldLift (world.shapeKind layout.ty)) == .adt do
    throw "variant path requested for non-variant world type"
  let declaration ← RuntimeMetadata.adtDeclarationInWorld context.runtime layout.ty
  let some name := declaration.variantNames[index]?
    | throw "canonical raw variant name absent for world projection"
  pure (.variant name)

def validityHooksInWorld (prepared : CompilerFactAdapters.Prepared)
    (types : RuntimeArrayQueries.Access S) (machine : ValidityVisitor.Hooks P S C E Fn Abi Pad) :
    ValidityVisitor.Hooks P S C E Fn Abi Pad :=
  let run := fun {A} (action : TypeArena.WorldM A) => RuntimeArrayQueries.perform types action
  {machine with
    classify := fun _ ty => run (CompilerFactAdapters.validityKindInWorld prepared ty)
    metadataTail := fun _ ty => run (CompilerFactAdapters.metadataTailInWorld prepared ty)
    unitLayout := fun _ => run (CompilerFacts.unitLayoutInWorld prepared.context)
    typeName := fun _ ty => run (CompilerFactAdapters.typeNameInWorld prepared ty)
    opsemInhabited := fun _ ty => run (CompilerFacts.booleanInWorld prepared.context ty "opsem_inhabited")
    isFreeze := fun _ ty => run (CompilerFacts.booleanInWorld prepared.context ty "is_freeze")
    fieldPath := fun _ layout index child => run (fieldPathInWorld prepared.context layout index child)
    variantPath := fun _ layout index => run (variantPathInWorld prepared.context layout index)}

private def lift (value : Result A) : EStateM StepError S A :=
  match value with
  | .ok value => pure value
  | .error error => throw (.invalidProgram error)

/-- Bind diagnostic paths using the actual projected child type supplied by the
visitor, including dynamically unpacked values and Box allocator projections. -/
def validityHooks (prepared : CompilerFactAdapters.Prepared)
    (machine : ValidityVisitor.Hooks P S C E Fn Abi Pad) :
    ValidityVisitor.Hooks P S C E Fn Abi Pad :=
  { CompilerFactAdapters.validityHooks prepared machine with
    fieldPath := fun _ layout index childType =>
      lift (fieldPath prepared.context layout index childType)
    variantPath := fun _ layout index =>
      lift (variantPath prepared.context layout index) }

end Miri.Input.CompilerPaths
