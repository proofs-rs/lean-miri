import Miri.Input.WorldNormalization

/-! Pinned struct_tail_raw and ptr_metadata_ty_or_tail, with stateful field
substitution supplied by the single execution universe. Tuple/pattern tail
steps do not perform an extra normalization query. Dynamic metadata uses the raw
DynMetadata lang-item identity and generic header; no query result decides its type. -/
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

/-- Pinned `ptr_metadata_ty_or_tail`: instantiate the raw DynMetadata lang
item with the exact dynamic tail. No queried metadata type identity is used. -/
def dynMetadataType (tail : TypeId) : WorldM TypeId := do
  let world ← get
  unless (← lift (world.shapeKind tail)) == .dynamicTraitObject do
    throw "DynMetadata constructor requires a dynamic tail"
  let declarations := world.definitions.filter fun source =>
    source.adtDeclaration.any (·.langItem == some "dyn_metadata")
  let #[source] := declarations | throw "raw DynMetadata declaration missing or ambiguous"
  let some declaration := source.adtDeclaration | throw "raw DynMetadata declaration absent"
  let some template := source.genericTemplate | throw "raw DynMetadata generic header absent"
  lift (declaration.validate template)
  unless declaration.kind == .structKind && template.parameters == #[.type] do
    throw "raw DynMetadata declaration has an invalid kind or generic header"
  let identity : GenericSubstitution.DefinitionIdentity := ⟨source.crateIndex,source.index⟩
  let _ ← lift (world.definitionRef identity)
  unless template.typeExpression == .definition .type "adt" identity
      (.cons (.parameter .type 0) .nil) do
    throw "raw DynMetadata generic header has a mismatched physical owner"
  World.internType (.adt identity #[.Type tail])

structure EffectContext (m : Type → Type) where
  normalizeType : Nat → TypeId → m TypeId
  unitType : TypeId
  usizeType : TypeId
  fieldType : TypeId → Nat → Nat → m TypeId

section EffectfulTail
variable {m : Type → Type} [Monad m] [MonadStateOf World m]
  [MonadExceptOf String m] [MonadLiftT (Except String) m] [MonadLiftT WorldM m]
private def tail (context : EffectContext m) : Nat → TypeId → m TypeId
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
    if let .constructed (.patternType base _) := view then
      return ← tail context fuel base
    if let .constructed (.tuple fields) := view then
      match fields.back? with
      | none => return id | some last => return ← tail context fuel last
    unless (← lift (world.shapeKind id)) == .adt do return id
    let declaration ← adtDeclaration id
    unless declaration.kind == .structKind do return id
    let fields := declaration.fields.filter (·.variantIndex == 0)
    let some last := fields.back? | return id
    -- The owning field callback normalizes the raw field term exactly once.
    -- Resolving a raw constant alias to a TypeId first is not an admission.
    let child ← context.fieldType id 0 last.fieldIndex
    tail context fuel child

def metadataTailEffectful (context : EffectContext m) (fuel : Nat) (id : TypeId) : m TypeId := do
  -- struct_tail_raw starts from self; only an ADT field invokes normalize.
  -- Tuple/Pattern steps must not evaluate unrelated constant bounds.
  tail context fuel id

def pointerMetadataTypeEffectful (context : EffectContext m) (fuel : Nat) (id : TypeId) : m TypeId := do
  let id ← metadataTailEffectful context fuel id
  let world ← get
  match ← lift (world.shapeKind id) with
  | .str | .slice => pure context.usizeType
  | .unsafeBinder => throw "pointer metadata for UnsafeBinder is unimplemented in pinned rustc"
  | .alias => throw "pointer metadata tail remains an unresolved alias"
  | .dynamicTraitObject => dynMetadataType id
  | _ => pure context.unitType

end EffectfulTail

private def Context.effectful (context : Context) : EffectContext WorldM := {
  normalizeType := WorldNormalization.normalizeType context.normalization 10000
  unitType := context.unitType
  usizeType := context.usizeType
  fieldType := context.fieldType }

def metadataTail (context : Context) (fuel : Nat) (id : TypeId) : WorldM TypeId :=
  metadataTailEffectful context.effectful fuel id

def pointerMetadataType (context : Context) (fuel : Nat) (id : TypeId) : WorldM TypeId :=
  pointerMetadataTypeEffectful context.effectful fuel id
end Miri.Input.WorldTypeMetadata
