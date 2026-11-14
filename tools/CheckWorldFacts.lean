import Miri.Input.CompilerWorldFacts
import Miri.Input.Decoder
open Lean Miri.Input Miri.Input.TypeArena
private def must (value : Except String A) : IO A :=
  match value with | .ok result => pure result | .error error => throw (IO.userError error)
private def check (value : Bool) (message : String) : WorldM Unit :=
  unless value do throw message

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fresh novel-array source input")
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let source := decoded.document
  let runtime ← must ((RuntimeMetadata.ofDocument source).mapError toString)
  let context ← must (CompilerFacts.ofProgram runtime (← must (lowerProgram source)))
  let initial ← must (World.ofDocument source)
  let action : WorldM Unit := do
    let mut root := source.queries.primitives.bool
    for _ in [:64] do root ← World.internType (.tuple #[root,root])
    let before ← get
    for key in #["is_monomorphic_enough", "is_monomorphic", "is_sized", "opsem_inhabited", "is_freeze", "is_unpin", "is_unsafe_unpin"] do
      check (← CompilerFacts.booleanInWorld context root key) s!"shared DAG {key} false"
    check (!(← CompilerFacts.booleanInWorld context root "needs_drop")) "shared boolean DAG needs drop"
    check ((← get).typeCount == before.typeCount) "read-only shared DAG facts created unrelated types"
    let reference ← World.internType (.reference source.queries.primitives.bool .Mut .Static)
    check (← CompilerFacts.booleanInWorld context reference "has_erasable_regions") "static region not erasable"
    let erased ← CompilerFacts.requiredTypeInWorld context reference "normalized"
    check (!(← CompilerFacts.booleanInWorld context erased "has_erasable_regions")) "normalized reference retains erasable region"
    let parameter ← World.internType (.reference source.queries.primitives.bool .Mut (.EarlyParameter 0 "'a"))
    check (!(← CompilerFacts.booleanInWorld context parameter "is_monomorphic_enough")) "region parameter not included in has_param"
    check (← CompilerFacts.booleanInWorld context parameter "is_monomorphic") "region parameter incorrectly treated as non-region parameter"
    let nominal := source.types.filter fun node => match node.shape with
      | .adt data => (source.definitions[data.definition]?).any (·.crateIndex == 0)
      | _ => false
    unless nominal.size == 1 do throw "fixture must retain exactly one source local nominal type"
    let some nominal := nominal[0]? | throw "source nominal type absent"
    let length ← World.internConstant (.Value source.queries.primitives.usize
      ⟨#[.Leaf 2 (← get).pointerBytes],0⟩)
    let array ← World.internType (.array nominal.id length)
    check (array >= source.types.size) "nominal array was eagerly seeded"
    for key in #["is_monomorphic_enough", "opsem_inhabited", "is_sized", "is_freeze", "is_unpin", "is_unsafe_unpin"] do
      check (← CompilerFacts.booleanInWorld context array key) s!"new nominal array {key} false"
    check (!(← CompilerFacts.booleanInWorld context array "needs_drop")) "Copy nominal array needs drop"
    check ((← CompilerFacts.requiredTypeInWorld context array "discriminant_type") == source.queries.primitives.u8)
      "new array discriminant type differs from u8"
  let (_,_) ← must (action.run initial)
  IO.println "PASS single-World facts on 64-level shared DAG, region flags/erasure, and novel nominal array with raw trait fulfillment"
