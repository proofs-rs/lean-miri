import Miri.Input.CompilerFacts
import Miri.Input.CompilerPrimitiveFacts
import Miri.Interpreter.Discriminant

/-! Actual rustc Ty::discriminant_ty, ADT/coroutine discriminants and
PrimitiveExt::to_int_ty evidence for interpret/discriminant.rs. Values remain
compiler u128 bits; declaration indices, encoded tags and signed discriminants
are not conflated. -/
namespace Miri.Input.CompilerDiscriminantFacts
open Lean Miri.ABI Miri.Interpreter
private def data (context : CompilerFacts.Context) (id : TypeId) : Except String DiscriminantInfo := do
  let source ← context.runtime.node id |>.mapError toString
  if id >= context.runtime.source.types.size then
    if let some result := ConstructedDiscriminants.info source.shape then return result
  let some facts := source.compilerFacts | throw "missing discriminant compiler facts"
  unless facts.typingEnvironment == "fully_monomorphized" do
    throw "discriminant compiler environment mismatch"
  let some query := facts.discriminants | throw "missing discriminant compiler query"
  pure query

def discriminantLayout (context : CompilerFacts.Context) (ty : TypeId) :
    Except String (TyAndLayout TypeId) := do
  CompilerFacts.layoutOf context (← CompilerFacts.requiredType context ty "discriminant_type")
private def primitiveKey : Primitive → Except String String
  | .Int integer signed => pure ((if signed then "i" else "u") ++ match integer with
      | .I8 => "8" | .I16 => "16" | .I32 => "32" | .I64 => "64" | .I128 => "128")
  | .Pointer _ => pure "pointer_tag_integer"
  | .Float _ => throw "source invariant: floating primitive has no integer tag type"

/-- Pointer tags use rustc's default ptr_sized_integer query (including its
source nondefault-address-space limitation), never a guessed usize/layout. -/
def tagLayout (context : CompilerFacts.Context) (tag : Scalar) : Except String (TyAndLayout TypeId) := do
  let key ← primitiveKey tag.primitive
  CompilerPrimitiveFacts.primitiveLayout context.runtime key
private def values (context : CompilerFacts.Context) (info : DiscriminantInfo) :
    Except String (Array (Nat × TypeId × U128)) :=
  info.values.mapM fun value => do
    unless value.variant < 2^32 do throw "compiler variant index exceeds u32"
    let _ ← context.runtime.node value.typeId |>.mapError toString
    unless value.bits < 2^128 do throw "compiler discriminant exceeds u128"
    pure (value.variant,value.typeId,BitVec.ofNat 128 value.bits)

def discriminantValue (context : CompilerFacts.Context) (ty variant : Nat) :
    Except String (Option (TypeId × U128)) := do
  let info ← data context ty
  let has := info.hasDiscriminants
  let entries ← values context info
  if !has then
    unless entries.isEmpty do throw "non-discriminant type has discriminant values"
    return none
  let matching := entries.filter (·.1 == variant)
  unless matching.size == 1 do throw "missing or duplicate compiler variant discriminant"
  let some (_,discrTy,bits) := matching[0]? | throw "missing compiler discriminant"
  unless discrTy == (← discriminantLayout context ty).ty do throw "compiler discriminant type mismatch"
  pure (some (discrTy,bits))

def variantForDiscriminant (context : CompilerFacts.Context) (ty : TypeId) (bits : U128) :
    Except String (Option Nat) := do
  let info ← data context ty
  unless info.hasDiscriminants do
    throw "source invariant: tagged layout has no ADT/coroutine discriminants"
  let entries ← values context info
  let matching := entries.filter (·.2.2 == bits)
  if matching.size > 1 then throw "ambiguous compiler discriminant value"
  pure (matching[0]?.map (·.1))

def adtVariantCount (context : CompilerFacts.Context) (ty : TypeId) : Except String Nat := do
  let info ← data context ty
  let some count := info.adtVariantCount | throw "source invariant: ADT variant count requested for non-ADT"
  pure count
private def lift (value : Except String A) : EStateM StepError S A :=
  match value with
  | .ok value => pure value
  | .error reason => throw (.unsupported s!"compiler discriminant query: {reason}")

def hooks (context : CompilerFacts.Context) (base : DiscriminantHooks P S C V) :
    DiscriminantHooks P S C V :=
  { base with
    runtimeTarget := context.runtime.target
    discriminantLayout := fun _ ty => lift (discriminantLayout context ty)
    tagLayout := fun _ tag => lift (tagLayout context tag)
    discriminantValue := fun _ ty variant => lift (discriminantValue context ty variant)
    variantForDiscriminant := fun _ ty bits => lift (variantForDiscriminant context ty bits)
    adtVariantCount := fun _ ty => lift (adtVariantCount context ty) }
end Miri.Input.CompilerDiscriminantFacts
