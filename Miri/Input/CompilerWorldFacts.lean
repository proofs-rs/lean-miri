import Miri.Input.CompilerFacts
import Miri.Input.WorldNormalization
import Miri.Input.WorldTypeFlags
import Miri.Input.WorldInhabitedness
import Miri.Input.WorldNeedsDrop
import Miri.Input.WorldTrivialAutoTraits
import Miri.Input.WorldDiscriminantType

/-! Execution compiler queries. Every constructor/layout action runs in the
caller's one WorldM; source-only query functions are never synthetic-ID fallbacks. -/
namespace Miri.Input.CompilerFacts
open Lean Miri.ABI Miri.Memory Miri.Interpreter TypeArena
private def worldLift [Monad m] [MonadExceptOf String m] (value : Except String A) : m A :=
  match value with | .ok result => pure result | .error error => throw error
private def queryFuel : WorldM Nat := do
  let world ← get
  pure (max 256 (world.typeCount + world.constantCount + 1))
private def materialBoolean (id : TypeId) (key : String) : WorldM (Option Bool) := do
  if let .material source ← worldLift ((← get).lookupType id) then
    if let some facts := source.compilerFacts then
      unless facts.typingEnvironment == "fully_monomorphized" do throw "compiler world boolean environment mismatch"
      return (facts.booleanQueries.find? (·.1 == key)).map (·.2)
  pure none
private def constructor (id : TypeId) : WorldM TypeArena.Constructor := do
  let world ← get
  match ← worldLift (world.lookupType id) with
  | .constructed value => pure value
  | .material source =>
    let some value ← worldLift (world.materialKey source)
      | throw "compiler world query requires an unported source constructor"
    pure value

def normalizeInWorld (context : Context) (id : TypeId) : WorldM TypeId := do
  WorldNormalization.normalizeType context.runtime.normalizationContext 10000 (← queryFuel) id

def primitiveTypeInWorld (context : Context) (key : String) : WorldM TypeId := do
  let id ← worldLift (CompilerPrimitiveFacts.primitiveType context.runtime key)
  let _ ← worldLift ((← get).lookupType id)
  pure id

def layoutOfInWorld (context : Context) (id : TypeId) : WorldM (TyAndLayout TypeId) :=
  RuntimeMetadata.layoutInWorld context.runtime id

def unitLayoutInWorld (context : Context) : WorldM (TyAndLayout TypeId) := do
  layoutOfInWorld context (← primitiveTypeInWorld context "unit")

private def sourceTrait (context : Context) (id : TypeId) (key : String) : WorldM Bool := do
  let lang ← match key with
    | "is_freeze" => pure "freeze" | "is_unpin" => pure "unpin"
    | "is_unsafe_unpin" => pure "unsafe_unpin" | _ => throw "unknown world auto-trait query"
  let source := context.runtime.normalizationContext
  let declarations := source.traits.traits.filter (·.langItem == some lang)
  unless declarations.size == 1 do throw s!"world trait declaration absent or duplicated: {lang}"
  let some declaration := declarations[0]? | throw "world trait declaration absent"
  let term ← worldLift (GenericInstantiationWorld.ofType (← get) (← queryFuel) id)
  match ← worldLift (AliasRuntime.solveGoal source (← queryFuel) 10000
      ⟨.positive,⟨declaration.definition,#[term]⟩⟩) with
  | .proven _ => pure true | .noSolution => pure false
  | .ambiguous reason => throw s!"world auto-trait query is ambiguous: {reason}"

/-- Original-kind flags stay unnormalized. Sized/drop/inhabitedness and public
trait queries execute their respective source normalization contracts. -/
def booleanInWorld (context : Context) (id : TypeId) (key : String) : WorldM Bool := do
  let kind ← worldLift ((← get).shapeKind id)
  if key == "is_dynamic" then return kind == .dynamicTraitObject
  if key == "is_too_generic" then return kind == .alias
  if #["has_erasable_regions", "is_monomorphic_enough", "is_monomorphic"].contains key then
    return ← worldLift (WorldTypeFlags.query (← get) key (← queryFuel) id)
  if let some result ← materialBoolean id key then return result
  if key == "is_sized" then return ← RuntimeMetadata.sizedInWorld context.runtime id
  if key == "needs_drop" then return ← WorldNeedsDrop.query context.runtime (← queryFuel) id
  if key == "opsem_inhabited" then return ← WorldInhabitedness.query context.runtime (← queryFuel) id
  if #["is_freeze", "is_unpin", "is_unsafe_unpin"].contains key then
    let normalized ← normalizeInWorld context id
    if let some result ← materialBoolean normalized key then return result
    if ← worldLift (WorldTrivialAutoTraits.query (← get) (← queryFuel) normalized) then return true
    return ← sourceTrait context normalized key
  if key == "is_like_maybe_dangling" && kind == .coroutine then return true
  if #["is_box", "is_global_box", "is_unsafe_cell", "is_c_void", "is_simd", "is_like_maybe_dangling"].contains key then
    if kind != .adt then return false
    let declaration ← RuntimeMetadata.adtDeclarationInWorld context.runtime id
    if key == "is_box" then return declaration.langItem == some "owned_box"
    if key == "is_unsafe_cell" then return declaration.langItem == some "unsafe_cell"
    if key == "is_c_void" then return declaration.langItem == some "c_void"
    if key == "is_simd" then return declaration.representation.simd
    if key == "is_like_maybe_dangling" then
      return declaration.langItem == some "maybe_dangling" || declaration.langItem == some "manually_drop"
    unless declaration.langItem == some "owned_box" do return false
    let .adt _ args ← constructor id | throw "Box world constructor kind mismatch"
    let some allocator := args[1]? | return true
    let .Type allocator := allocator | throw "Box allocator argument is not a type"
    unless (← worldLift ((← get).shapeKind allocator)) == .adt do return false
    return (← RuntimeMetadata.adtDeclarationInWorld context.runtime allocator).langItem == some "global_alloc"
  throw s!"unsupported compiler world boolean query: {key}"

private def queryView (id : TypeId) : WorldM TypeId := do
  let world ← get
  if let .material source ← worldLift (world.lookupType id) then
    if let some query := source.layoutQueryInputTypeId then
      unless query < world.materialTypes.size do throw "compiler query view escapes source prefix"
      return query
  pure id

private def boxedInWorld (context : Context) (id : TypeId) : WorldM (Option TypeId) := do
  unless ← booleanInWorld context id "is_box" do return none
  let .adt _ args ← constructor id | throw "Box query on a non-ADT world constructor"
  let some (MIR.GenericArg.Type child) := args[0]? | throw "Box world constructor lacks its pointee argument"
  let _ ← worldLift ((← get).lookupType child)
  pure (some child)

def optionalTypeInWorld (context : Context) (id : TypeId) (key : String) : WorldM (Option TypeId) := do
  let _ ← worldLift ((← get).lookupType id)
  let result ← if key == "normalized" then
      pure (some (← normalizeInWorld context id))
    else if key == "discriminant_type" then do
      let root ← normalizeInWorld context id
      pure (some (← WorldDiscriminantType.query {
        primitive := primitiveTypeInWorld context,
        normalize := fun _ ty => normalizeInWorld context ty } (← queryFuel) root))
    else if key == "metadata_tail" then
      pure (some (← RuntimeMetadata.metadataTailInWorld context.runtime id))
    else if key == "pointer_metadata_type" then
      pure (some (← RuntimeMetadata.pointerMetadataTypeInWorld context.runtime id))
    else if key == "boxed_type" || key == "builtin_deref_explicit" || key == "builtin_deref_implicit" then do
      let id ← queryView id
      if let some child ← boxedInWorld context id then return some child
      if key == "boxed_type" then return none
      let kind ← worldLift ((← get).shapeKind id)
      unless kind == .reference || kind == .rawPointer do return none
      match ← constructor id with
      | .reference child .. => pure (some child)
      | .rawPointer child _ => pure (if key == "builtin_deref_explicit" then some child else none)
      | _ => pure none
    else if key == "unsafe_binder_erased" then do
      let world ← get
      match ← worldLift (world.lookupType id) with
      | .constructed _ => pure none
      | .material source =>
        unless source.shapeKind == .unsafeBinder do return none
        let some facts := source.compilerFacts | throw "world unsafe-binder erasure source absent"
        let some (_,value) := facts.typeQueries.find? (·.1 == key) | throw "world residual binder erasure absent"
        pure value
    else do
      let .material source ← worldLift ((← get).lookupType id)
        | throw s!"compiler world type query is not migrated: {key}"
      let some facts := source.compilerFacts | throw "compiler world residual type facts absent"
      unless facts.typingEnvironment == "fully_monomorphized" do throw "compiler world type environment mismatch"
      let some (_,value) := facts.typeQueries.find? (·.1 == key) | throw s!"compiler world residual type query absent: {key}"
      pure value
  if let some result := result then let _ ← worldLift ((← get).lookupType result)
  pure result

def requiredTypeInWorld (context : Context) (id : TypeId) (key : String) : WorldM TypeId := do
  let some result ← optionalTypeInWorld context id key | throw s!"compiler world type query returned None: {key}"
  pure result

def builtinDerefInWorld (context : Context) (id : TypeId) (explicit : Bool) : WorldM (Option TypeId) :=
  optionalTypeInWorld context id (if explicit then "builtin_deref_explicit" else "builtin_deref_implicit")

def referencePointeeInWorld (_context : Context) (id : TypeId) : WorldM (TypeId × MIR.Mutability) := do
  let .reference child mutability _ ← constructor id | throw "reference pointee requested for another world type"
  pure (child,mutability)

def retagTypeShapeInWorld (context : Context) (id : TypeId) : WorldM Miri.TreeBorrows.RetagPipeline.RetagTypeShape := do
  let kind ← worldLift ((← get).shapeKind id)
  pure ⟨← booleanInWorld context id "is_global_box",kind == .reference,kind == .rawPointer,
    ← booleanInWorld context id "is_box"⟩

end Miri.Input.CompilerFacts
