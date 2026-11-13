import Miri.Input.CompilerWorldFacts
import Miri.Input.RuntimeArrayQueries
import Miri.Input.RuntimeEffectfulLayout

/-! Source compiler leaves for call.rs structural compatibility, evaluated in
one execution World. Raw declaration attributes remain distinct from layouts. -/
namespace Miri.Input.CompilerWorldCompatibility
open Miri.ABI Miri.Interpreter TypeArena
private def lift (value : Except String A) : WorldM A :=
  match value with | .ok result => pure result | .error error => throw error
private def constructor (ty : TypeId) : WorldM Constructor := do
  let world ← get
  match ← lift (world.lookupType ty) with
  | .constructed value => pure value
  | .material source =>
    let some value ← lift (world.materialKey source) | throw "compatibility source constructor unavailable"
    pure value

def kind (ty : TypeId) : WorldM (LayoutCompat.TypeKind TypeId) := do
  let world ← get
  match ← lift (world.shapeKind ty) with
  | .unsafeBinder => return .unsafeBinder
  | .bool | .float | .foreign | .str | .slice | .dynamicTraitObject => return .other
  | _ => pure ()
  match ← constructor ty with
  | .tuple _ => pure .tuple | .never => pure .never
  | .functionDefinition .. => pure .functionDefinition
  | .closure .. => pure .closure | .coroutine .. => pure .coroutine
  | .coroutineClosure .. => pure .coroutineClosure
  | .array child _ => pure (.array child) | .adt .. => pure .adt
  | .patternType base _ => pure (.pattern base) | .alias .. => pure .alias
  | .reference child .. => pure (.reference child)
  | .rawPointer child _ => pure (.rawPointer child)
  | .functionPointer .. => pure .functionPointer
  | .integer _ integer => pure (.integer integer) | .char => pure .char
  | _ => pure .other

def adt (metadata : RuntimeMetadata) (ty : TypeId) : WorldM (LayoutCompat.AdtInfo TypeId) := do
  let source ← RuntimeMetadata.adtDeclarationInWorld metadata ty
  let .adt owner arguments ← constructor ty | throw "compatibility ADT source constructor mismatch"
  let kind := match source.kind with
    | .structKind => LayoutCompat.AdtKind.Struct | .unionKind => .Union | .enumKind => .Enum
  let mut variants := #[]
  for variant in [:source.variants.size] do
    let some declaration := source.variants[variant]? | throw "compatibility variant source absent"
    let mut fields := #[]
    for index in [:declaration.fieldCount] do
      let matchingFields := source.fields.filter fun field => field.variantIndex == variant && field.fieldIndex == index
      unless matchingFields.size == 1 do throw "compatibility field source missing or duplicated"
      let some field := matchingFields[0]? | throw "compatibility field source absent"
      -- call.rs keeps field.ty(tcx,args) raw; identicalCTypes requests
      -- normalization separately at its exact source call site.
      let fuel := max 256 ((← get).typeCount + (← get).constantCount + 1)
      let term ← lift (GenericInstantiationWorld.instantiateFieldTerm (← get) fuel owner arguments variant index)
      let fieldType ← GenericInstantiationWorld.resolveType fuel term
      fields := fields.push ⟨field.fieldName,fieldType⟩
    variants := variants.push fields
  pure ⟨kind,source.representation.transparent,source.representation.c,source.representation.rust,variants⟩

def reprEqualUpToSeed (metadata : RuntimeMetadata) (left right : TypeId) : WorldM Bool := do
  let a := (← RuntimeMetadata.adtDeclarationInWorld metadata left).representation
  let b := (← RuntimeMetadata.adtDeclarationInWorld metadata right).representation
  pure (a.integer == b.integer && a.alignBytes == b.alignBytes &&
    a.packBytes == b.packBytes && a.flagsBits == b.flagsBits && a.scalableElement == b.scalableElement)

def itemName (ty : TypeId) : WorldM String := do
  let .adt identity _ ← constructor ty | throw "compatibility item_name requires ADT"
  let world ← get
  let reference ← lift (world.definitionRef identity)
  let some definition := world.definitions[reference]? | throw "compatibility ADT definition absent"
  let some path := definition.rawPath | throw "compatibility item_name raw DefKey absent"
  let some component := path.components.back? | throw "compatibility item_name empty DefKey"
  unless component.kind == "type" do throw "compatibility item_name non-type DefKey"
  let some name := component.name | throw "compatibility item_name source symbol absent"
  pure name

def queries (context : CompilerFacts.Context) (types : RuntimeArrayQueries.Access S)
    (provider : RuntimeEffectfulLayout.Provider S := RuntimeEffectfulLayout.unavailable) :
    LayoutCompat.Queries TypeId S :=
  let run := fun {A} (action : WorldM A) => RuntimeArrayQueries.perform types action
  { target := context.runtime.target
    kind := fun ty => run (kind ty)
    adt := fun ty => run (adt context.runtime ty)
    field := fun layout index => RuntimeEffectfulLayout.fieldLayout types provider CompilerTypingEnv.fullyMonomorphized none context.runtime layout index
    layoutOf := fun ty => RuntimeEffectfulLayout.layout types provider CompilerTypingEnv.fullyMonomorphized none context.runtime ty
    unitLayout := run (CompilerFacts.unitLayoutInWorld context)
    eraseUnsafeBinder := fun ty => run (CompilerFacts.requiredTypeInWorld context ty "unsafe_binder_erased")
    normalize := fun ty => RuntimeEffectfulLayout.normalizeType types provider CompilerTypingEnv.fullyMonomorphized none context.runtime ty
    reprEqualUpToSeed := fun a b => run (reprEqualUpToSeed context.runtime a b)
    itemName := fun ty => run (itemName ty)
    nonnullOptimizationGuaranteed := fun ty => run do
      pure (← RuntimeMetadata.adtDeclarationInWorld context.runtime ty).nonnullOptimizationGuaranteed
    isGlobalBox := fun ty => run (CompilerFacts.booleanInWorld context ty "is_global_box")
    boxedType := fun ty => run (CompilerFacts.requiredTypeInWorld context ty "boxed_type")
    pointerMetadataType := fun ty => RuntimeEffectfulLayout.pointerMetadataType types provider CompilerTypingEnv.fullyMonomorphized none context.runtime ty }
end Miri.Input.CompilerWorldCompatibility
