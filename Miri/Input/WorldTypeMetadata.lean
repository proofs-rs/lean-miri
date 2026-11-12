import Miri.Input.WorldNormalization

/-! Pinned struct_tail_raw and ptr_metadata_ty_or_tail, with stateful field
substitution supplied by the single execution universe. Tuple/pattern tail
steps do not perform an extra normalization query. Dynamic metadata constructor
material is explicitly residual; no physical pointer layout decides its type. -/
namespace Miri.Input.WorldTypeMetadata
open TypeArena
structure Context where
  normalization : AliasRuntime.Context
  unitType : TypeId
  usizeType : TypeId
  fieldType : TypeId → Nat → Nat → WorldM TypeId
private def lift [Monad m] [MonadExceptOf String m] (value : Except String A) : m A :=
  match value with | .ok result => pure result | .error error => throw error

def adtDeclaration (id : TypeId) : WorldM AdtDeclaration.Material := do
  let world ← get
  let definition ← match ← lift (world.lookupType id) with
    | .material source => match source.shape with
      | .adt data => pure data.definition
      | _ => throw "metadata ADT declaration requested for another type"
    | .constructed (.adt identity _) => lift (world.definitionRef identity)
    | _ => throw "metadata ADT declaration requested for another constructor"
  let some source := world.definitions[definition]? | throw "metadata ADT definition absent"
  let some declaration := source.adtDeclaration | throw "metadata canonical ADT declaration absent"
  let some template := source.genericTemplate | throw "metadata ADT field template absent"
  lift (declaration.validate template)
  pure declaration

private def tail (context : Context) : Nat → TypeId → WorldM TypeId
  | 0, _ => throw "world metadata tail traversal exhausted"
  | fuel + 1, id => do
    let world ← get
    let view ← lift (world.lookupType id)
    if let .material source := view then
      match source.shape with
      | .patternType base _ => return ← tail context fuel base
      | .tuple fields => match fields.back? with
        | none => return id | some last => return ← tail context fuel last
      | _ => pure ()
    if let .constructed (.tuple fields) := view then
      match fields.back? with
      | none => return id | some last => return ← tail context fuel last
    unless (← lift (world.shapeKind id)) == .adt do return id
    let declaration ← adtDeclaration id
    unless declaration.kind == .structKind do return id
    let fields := declaration.fields.filter (·.variantIndex == 0)
    let some last := fields.back? | return id
    let child ← context.fieldType id 0 last.fieldIndex
    let child ← WorldNormalization.normalizeType context.normalization 10000 (fuel + 1) child
    tail context fuel child

def metadataTail (context : Context) (fuel : Nat) (id : TypeId) : WorldM TypeId := do
  let normalized ← WorldNormalization.normalizeType context.normalization 10000 fuel id
  tail context fuel normalized

def pointerMetadataType (context : Context) (fuel : Nat) (id : TypeId) : WorldM TypeId := do
  let id ← metadataTail context fuel id
  let world ← get
  match ← lift (world.shapeKind id) with
  | .str | .slice => pure context.usizeType
  | .unsafeBinder => throw "pointer metadata for UnsafeBinder is unimplemented in pinned rustc"
  | .alias => throw "pointer metadata tail remains an unresolved alias"
  | .dynamicTraitObject =>
    let .material source ← lift (world.lookupType id)
      | throw "dynamic metadata type requires its source DynMetadata constructor"
    let some facts := source.compilerFacts | throw "dynamic metadata constructor material absent"
    unless facts.typingEnvironment == "fully_monomorphized" do throw "dynamic metadata constructor environment mismatch"
    let some (_,some result) := facts.typeQueries.find? (·.1 == "pointer_metadata_type")
      | throw "dynamic DynMetadata constructor remains explicitly residual"
    unless result < world.materialTypes.size do throw "dynamic metadata source result escapes material prefix"
    let _ ← lift (world.lookupType result)
    pure result
  | _ => pure context.unitType

end Miri.Input.WorldTypeMetadata
