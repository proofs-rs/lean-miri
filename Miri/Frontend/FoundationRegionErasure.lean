import Miri.Frontend.FoundationPointer

/-! Pure region erasure for the closed structural source domain. Pinned rustc
uses erase_regions/normalize_erasing_regions before executable MIR and FnAbi.
Only Static/Erased references occur in this source format; mutability and every
non-region type component remain exact. Original source JSON is retained. -/
namespace Miri.Frontend.Foundation

def eraseRegions (ty : ConcreteType) : Except String ConcreteType := go 1024 ty
where
  go (fuel : Nat) (ty : ConcreteType) : Except String ConcreteType := do
    let .succ fuel := fuel | throw "region erasure recursion exhausted"
    match ty with
    | .primitive k n => return .primitive k n
    | .patternNotNull base => return .patternNotNull (← go fuel base)
    | .closure definition arguments => return .closure definition (← arguments.mapM (go fuel))
    | .nominal definition arguments => return .nominal definition (← arguments.mapM (go fuel))
    | .array element count => return .array (← go fuel element) count
    | .tuple fields => return .tuple (← fields.mapM (go fuel))
    | .pointer kind pointee =>
      let info ← pointerKindInfo kind
      let kind := if info.region.isSome then
          if info.mutability == .Mut then "reference_erased_mut" else "reference_erased_const"
        else kind
      return .pointer kind (← go fuel pointee)
    | .dynamicObject source =>
      unless source.region == "static" || source.region == "erased" do throw "dynamic region unsupported"
      let mapped ← mapExistentialM (go fuel) source
      return .dynamicObject {mapped with region := "erased"}
    | .functionPointer inputs output safety abi variadic =>
      return .functionPointer (← inputs.mapM (go fuel)) (← go fuel output) safety abi variadic

/-- HAS_FREE_REGIONS includes ReStatic and excludes ReErased in pinned
rustc_type_ir/sty/mod.rs; composite type flags include their children. -/
def hasErasableRegions (ty : ConcreteType) : Except String Bool := go 1024 ty
where
  go (fuel : Nat) (ty : ConcreteType) : Except String Bool := do
    let .succ fuel := fuel | throw "region flag recursion exhausted"
    match ty with
    | .primitive .. => return false
    | .patternNotNull base => go fuel base
    | .closure _ arguments => return (← arguments.mapM (go fuel)).any id
    | .nominal _ arguments => return (← arguments.mapM (go fuel)).any id
    | .array element _ => go fuel element
    | .tuple fields => return (← fields.mapM (go fuel)).any id
    | .pointer kind pointee =>
      let info ← pointerKindInfo kind
      return info.region == some .Static || (← go fuel pointee)
    | .dynamicObject source =>
      unless source.region == "static" || source.region == "erased" do throw "dynamic region unsupported"
      let args ← source.arguments.mapM (go fuel)
      let projections ← source.projections.mapM fun p => do
        return (← go fuel p.term) || (← p.arguments.mapM (go fuel)).any id
      return source.region == "static" || args.any id || projections.any id
    | .functionPointer inputs output .. =>
      return (← go fuel output) || (← inputs.mapM (go fuel)).any id

end Miri.Frontend.Foundation
