import Miri.Input.SourceCompilerRuntime
import Miri.Input.CompilerPrimitiveFacts

/-! Pinned rustc_middle/ty/sty.rs::Ty::{discriminant_ty,
discriminant_for_variant}. Default-repr enums with relative discriminants use
isize and their declaration indices. Non-enums have u8 and no value. -/
namespace Miri.Input.SourceCompilerDiscriminants
open Miri.ABI
private def node (runtime : RuntimeMetadata) (id : Nat) : Except String TypeNode :=
  runtime.node id |>.mapError toString

private def relativeEnum (runtime : RuntimeMetadata) (data : AdtShape) : Except String SourceTypes.Adt := do
  let some material := runtime.source.sourceMaterial | throw "Unsupported enum declaration source unavailable"
  let some source := material.physical | throw "Unsupported enum physical source unavailable"
  let some identity := runtime.source.definitions[data.definition]? | throw "Invalid enum canonical definition"
  let some declaration := source.definitions.find? (·.raw == identity) | throw "Unsupported enum source declaration unavailable"
  let some adt := declaration.adt | throw "Unsupported enum source shape unavailable"
  unless adt.kind == .enumKind && adt.representation.integer.isNone &&
      adt.variants.size == data.variants.size &&
      (adt.variants.zipIdx.all fun (variant,index) => variant.index == index && variant.discriminant == .relative index) do
    throw "Unsupported enum explicit discriminants"
  return adt

def layout (runtime : RuntimeMetadata) (id : Nat) : Except String (TyAndLayout TypeId) :=
  go (runtime.source.types.size + 1) id
where
  go (fuel id : Nat) : Except String (TyAndLayout TypeId) := do
    let .succ fuel := fuel | throw "Invalid cyclic source discriminant type graph"
    match (← node runtime id).shape with
    | .patternType inner _ | .unsafeBinder inner _ => go fuel inner
    | .adt data =>
      if data.kind == .enumKind then
        unless data.representation.integer.isNone do throw "Unsupported enum explicit integer representation"
        return ← CompilerPrimitiveFacts.primitiveLayout runtime "isize"
      CompilerPrimitiveFacts.primitiveLayout runtime "u8"
    | .coroutine .. => throw "Unsupported source coroutine discriminant representation"
    | .alias .. => throw "Unsupported source discriminant alias normalization"
    | _ => CompilerPrimitiveFacts.primitiveLayout runtime "u8"

def value (runtime : RuntimeMetadata) (id : Nat) (_variant : Nat) :
    Except String (Option (TypeId × U128)) := go (runtime.source.types.size + 1) id
where
  go (fuel id : Nat) : Except String (Option (TypeId × U128)) := do
    let .succ fuel := fuel | throw "Invalid cyclic source discriminant value graph"
    match (← node runtime id).shape with
    | .unsafeBinder inner _ => go fuel inner
    | .adt data =>
      if data.kind == .enumKind then
        let adt ← relativeEnum runtime data
        unless _variant < adt.variants.size do throw "Invalid enum discriminant variant index"
        let layout ← layout runtime id
        return some (layout.ty,BitVec.ofNat 128 _variant)
      pure none
    | .coroutine .. => throw "Unsupported source coroutine discriminant value"
    | .alias .. => throw "Unsupported source discriminant alias normalization"
    -- Unlike discriminant_ty, discriminant_for_variant does not unwrap Pat.
    | _ => pure none

def variantCount (runtime : RuntimeMetadata) (id : Nat) : Except String Nat := do
  let .adt data := (← node runtime id).shape
    | throw "Invalid source ADT variant count requested for non-ADT"
  return data.variants.size

def variantForDiscriminant (runtime : RuntimeMetadata) (id : Nat) (bits : U128) : Except String (Option Nat) := do
  let .adt data := (← node runtime id).shape | throw "Invalid enum discriminant source type"
  let adt ← relativeEnum runtime data
  let index := bits.toNat
  return if index < adt.variants.size then some index else none
end Miri.Input.SourceCompilerDiscriminants
