import Miri.Input.CompilerDiscriminantFacts
import Miri.Input.Decoder
open Lean Miri.Input
private def must (value : Except String A) : IO A :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected novel-array guest.json")
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let source := decoded.document
  let runtime ← must ((RuntimeMetadata.ofDocument source).mapError toString)
  let program ← must (lowerProgram source)
  let compiler ← must (CompilerFacts.ofProgram runtime program)
  let candidates := source.types.filter fun node => match node.shape with
    | .adt data => (source.definitions[data.definition]?).any (·.crateIndex == 0)
    | _ => false
  check (candidates.size == 1) "fixture must contain one local nominal type"
  let some nominal := candidates[0]? | throw (IO.userError "nominal material type absent")
  let initial ← must (TypeArena.World.ofDocument source)
  let (array,typeArena) ← must ((do
    let length ← TypeArena.World.internConstant (.Value source.queries.primitives.usize
      ⟨#[.Leaf 2 initial.pointerBytes],0⟩)
    TypeArena.World.internType (.array nominal.id length)).run initial)
  check (array >= source.types.size) "fixture array was eagerly seeded"
  let (pointer,typeArena) ← must ((TypeArena.World.internType (.rawPointer array .Mut)).run typeArena)
  let (reference,typeArena) ← must ((TypeArena.World.internType (.reference array .Mut .Erased)).run typeArena)
  let mut typeArena := typeArena
  for ty in #[array,pointer,reference] do
    let ((actual,layout,value),retained) ← must ((do
      let actual ← CompilerFacts.requiredTypeInWorld compiler ty "discriminant_type"
      let layout ← CompilerDiscriminantFacts.discriminantLayout compiler ty
      let value ← CompilerDiscriminantFacts.discriminantValue compiler ty 0
      pure (actual,layout,value)).run typeArena)
    typeArena := retained
    check (actual == source.queries.primitives.u8) "constructed discriminant type must be canonical u8"
    check (layout.ty == source.queries.primitives.u8 && layout.layout.size.bytes == 1)
      "constructed discriminant layout differs from u8"
    check value.isNone "constructed non-enum acquired discriminant enumeration"
    match (CompilerDiscriminantFacts.adtVariantCount compiler ty).run typeArena with
    | .ok _ => throw (IO.userError "constructed array/pointer acquired ADT variant count")
    | .error error =>
      check (error == "source invariant: ADT variant count requested for non-ADT")
        s!"non-ADT variant-count control failed for unrelated reason: {error}"
    match (CompilerDiscriminantFacts.variantForDiscriminant compiler ty 0).run typeArena with
    | .ok _ => throw (IO.userError "constructed non-enum accepted tag-to-variant lookup")
    | .error error =>
      check (error == "source invariant: tagged layout has no ADT/coroutine discriminants")
        s!"non-enum tag lookup control failed for unrelated reason: {error}"
    for key in #["is_monomorphic_enough", "opsem_inhabited", "is_sized", "is_freeze", "is_unpin", "is_unsafe_unpin"] do
      let (result,retained) ← must ((CompilerFacts.booleanInWorld compiler ty key).run typeArena)
      typeArena := retained
      check result s!"constructed {key} query failed"
    let (drop,retained) ← must ((CompilerFacts.booleanInWorld compiler ty "needs_drop").run typeArena)
    typeArena := retained
    check (!drop) "Copy constructor unexpectedly needs drop"
  IO.println "PASS novel nominal array and nested pointer/reference compiler facts, layouts and non-enum discriminants without eager rows"
