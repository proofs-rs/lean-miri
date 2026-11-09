import Miri.Input.CompilerLibcTypeLayouts
import Miri.Input.RuntimeArrayQueries

/-! Compiler-backed helpers.rs:280–312: libc array construction and named
non-enum ADT field projection. Names come from compiler field declarations;
neither offsets nor layout equality establish field/type identity. -/
namespace Miri.Input.CompilerNamedFields
open Lean Miri.ABI Miri.Interpreter

def fieldIndex (runtime : RuntimeMetadata) (parent : LocalLayout) (name : String) :
    Except StepError Nat := do
  let node ← runtime.node parent.ty |>.mapError (fun e => StepError.unsupported (toString e))
  let parse : Except String Nat := do
    let .adt data := node.shape | throw "named field source requires ADT"
    unless data.kind == .structKind || data.kind == .unionKind do
      throw "named field source requires non-enum ADT"
    unless data.variants.size == 1 do throw "non-enum ADT has invalid variant declarations"
    let some variant := data.variants[0]? | throw "missing non-enum variant"
    let matching := variant.fields.filter (·.name == name)
    unless matching.size == 1 do throw s!"missing or ambiguous compiler field {name}"
    let some field := matching[0]? | throw "missing named field"
    pure field.index
  let index ← parse.mapError StepError.invalidProgram
  -- Require the exact source field projection to be available as well.
  let _ ← runtime.field parent index |>.mapError (fun e => StepError.unsupported (toString e))
  pure index

def libcArrayLayout (runtime : RuntimeMetadata) (arrays : RuntimeArrayQueries.Access S)
    (key : String) (count : UInt64) : EStateM StepError S LocalLayout := do
  let element ← match CompilerLibcTypeLayouts.layout runtime key with
    | .ok value => pure value
    | .error reason => throw (.unsupported s!"libc array element query {key}: {reason}")
  RuntimeArrayQueries.arrayLayout arrays element.ty count

def iovecArrayLayout (runtime : RuntimeMetadata) (arrays : RuntimeArrayQueries.Access S)
    (count : UInt64) : EStateM StepError S LocalLayout :=
  libcArrayLayout runtime arrays "iovec" count
end Miri.Input.CompilerNamedFields
