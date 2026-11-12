import Miri.Input.CompilerWorldFacts
import Miri.Input.RuntimeArrayQueries
import Miri.Input.WorldTypeMetadata
import Miri.Interpreter.Discriminant

/-! Discriminant queries use the execution-owned type universe. Ordinary
constructors and struct/union counts follow pinned ty/sty.rs and raw ADT
metadata. Default enum values follow raw relative declarations in the active world.
Explicit expressions and coroutine enumeration retain residual compiler evidence. -/
namespace Miri.Input.CompilerDiscriminantFacts
open Lean Miri.ABI Miri.Interpreter TypeArena
private def lift [Monad m] [MonadExceptOf String m] (value : Except String α) : m α :=
  match value with | .ok value => pure value | .error error => throw error

private def data (context : CompilerFacts.Context) (id : TypeId) : WorldM DiscriminantInfo := do
  let id ← if (← lift ((← get).shapeKind id)) == .alias then
      CompilerFacts.normalizeInWorld context id else pure id
  let world ← get
  let kind ← lift (world.shapeKind id)
  if kind == .alias then throw "discriminant alias remained unresolved"
  if kind == .adt then
    let declaration ← WorldTypeMetadata.adtDeclaration id
    if declaration.kind != .enumKind then
      return ⟨false,some declaration.variantCount,#[]⟩
    if let some values ← lift (RelativeDiscriminants.values (context.runtime.target.pointerSize.bytes.toNat * 8) declaration) then
      let ty ← CompilerFacts.requiredTypeInWorld context id "discriminant_type"
      return ⟨true,some declaration.variantCount,values.zipIdx.map fun (bits,index) => ⟨index,ty,bits.toNat⟩⟩
  else if kind != .coroutine && kind != .unsafeBinder then
    return ⟨false,none,#[]⟩
  match ← lift (world.lookupType id) with
  | .material source =>
    let some facts := source.compilerFacts | throw "missing discriminant compiler facts"
    unless facts.typingEnvironment == "fully_monomorphized" do
      throw "discriminant compiler environment mismatch"
    let some query := facts.discriminants | throw "missing discriminant compiler query"
    if kind == .adt || kind == .coroutine then
      unless query.hasDiscriminants do throw "enum/coroutine residual has no discriminants"
      let count ← if kind == .adt then do
          let declaration ← WorldTypeMetadata.adtDeclaration id
          unless query.adtVariantCount == some declaration.variantCount do
            throw "enum residual variant count differs from raw declaration"
          pure declaration.variantCount
        else do
          unless query.adtVariantCount.isNone do throw "coroutine residual has an ADT variant count"
          pure query.values.size
      unless query.values.map (·.variant) == Array.range count do
        throw "residual discriminant variant domain differs from raw source"
      let ty ← CompilerFacts.requiredTypeInWorld context id "discriminant_type"
      unless query.values.all (·.typeId == ty) do throw "residual discriminant type differs from raw representation"
    pure query
  | .constructed (.adt _ _) =>
    throw "constructed enum discriminant values require unported raw CTFE material"
  | .constructed (.coroutine ..) =>
    throw "constructed coroutine discriminants require unported coroutine state material"
  | .constructed _ => throw "discriminant enumeration source constructor mismatch"

def discriminantLayout (context : CompilerFacts.Context) (ty : TypeId) : WorldM (TyAndLayout TypeId) := do
  let discriminant ← CompilerFacts.requiredTypeInWorld context ty "discriminant_type"
  CompilerFacts.layoutOfInWorld context discriminant
private def primitiveKey : Primitive → Except String String
  | .Int integer signed => pure ((if signed then "i" else "u") ++ match integer with
      | .I8 => "8" | .I16 => "16" | .I32 => "32" | .I64 => "64" | .I128 => "128")
  | .Pointer _ => pure "pointer_tag_integer"
  | .Float _ => throw "source invariant: floating primitive has no integer tag type"

def tagLayout (context : CompilerFacts.Context) (tag : Scalar) : WorldM (TyAndLayout TypeId) := do
  let key ← lift (primitiveKey tag.primitive)
  CompilerFacts.layoutOfInWorld context (← CompilerFacts.primitiveTypeInWorld context key)

private def values (info : DiscriminantInfo) : WorldM (Array (Nat × TypeId × U128)) :=
  info.values.mapM fun value => do
    unless value.variant < 2^32 do throw "compiler variant index exceeds u32"
    let _ ← lift ((← get).lookupType value.typeId)
    unless value.bits < 2^128 do throw "compiler discriminant exceeds u128"
    pure (value.variant,value.typeId,BitVec.ofNat 128 value.bits)

def discriminantValue (context : CompilerFacts.Context) (ty variant : Nat) :
    WorldM (Option (TypeId × U128)) := do
  let info ← data context ty
  let entries ← values info
  if !info.hasDiscriminants then
    unless entries.isEmpty do throw "non-discriminant type has discriminant values"
    return none
  let matching := entries.filter (·.1 == variant)
  unless matching.size == 1 do throw "missing or duplicate compiler variant discriminant"
  let some (_,discrTy,bits) := matching[0]? | throw "missing compiler discriminant"
  unless discrTy == (← discriminantLayout context ty).ty do throw "compiler discriminant type mismatch"
  pure (some (discrTy,bits))

def variantForDiscriminant (context : CompilerFacts.Context) (ty : TypeId) (bits : U128) :
    WorldM (Option Nat) := do
  let info ← data context ty
  unless info.hasDiscriminants do
    throw "source invariant: tagged layout has no ADT/coroutine discriminants"
  let entries ← values info
  let matching := entries.filter (·.2.2 == bits)
  if matching.size > 1 then throw "ambiguous compiler discriminant value"
  pure (matching[0]?.map (·.1))

def adtVariantCount (context : CompilerFacts.Context) (ty : TypeId) : WorldM Nat := do
  if (← lift ((← get).shapeKind ty)) == .adt then
    return (← WorldTypeMetadata.adtDeclaration ty).variantCount
  let info ← data context ty
  let some count := info.adtVariantCount | throw "source invariant: ADT variant count requested for non-ADT"
  pure count

def hooks (context : CompilerFacts.Context) (types : RuntimeArrayQueries.Access S)
    (base : DiscriminantHooks P S C V) : DiscriminantHooks P S C V :=
  {base with
    runtimeTarget := context.runtime.target
    discriminantLayout := fun _ ty => RuntimeArrayQueries.perform types (discriminantLayout context ty)
    tagLayout := fun _ tag => RuntimeArrayQueries.perform types (tagLayout context tag)
    discriminantValue := fun _ ty variant => RuntimeArrayQueries.perform types (discriminantValue context ty variant)
    variantForDiscriminant := fun _ ty bits => RuntimeArrayQueries.perform types (variantForDiscriminant context ty bits)
    adtVariantCount := fun _ ty => RuntimeArrayQueries.perform types (adtVariantCount context ty)}
end Miri.Input.CompilerDiscriminantFacts
