import Miri.Input.CompilerLibcTypeLayouts
import Miri.Input.RuntimeArrayQueries

/-! Compiler-backed helpers.rs:280–312: libc array construction and named
non-enum ADT field projection. Names come from compiler field declarations;
neither offsets nor layout equality establish field/type identity. -/
namespace Miri.Input.CompilerNamedFields
open Lean Miri.ABI Miri.Interpreter

/-- Name lookup uses raw declaration symbols only. It does not request a field
layout or normalize its type before the caller actually projects that field. -/
def fieldIndex (types : RuntimeArrayQueries.Access S) (parent : LocalLayout) (name : String) :
    EStateM StepError S Nat := do
  let runtime := (types.get (← get)).metadata
  let result ← RuntimeArrayQueries.perform types do
    unless (← RuntimeMetadata.shapeKindInWorld runtime parent.ty) == .adt do
      return Except.error (StepError.invalidProgram "named field source requires ADT")
    let declaration ← RuntimeMetadata.adtDeclarationInWorld runtime parent.ty
    unless declaration.kind == .structKind || declaration.kind == .unionKind do
      return Except.error (StepError.invalidProgram "named field source requires non-enum ADT")
    unless declaration.variants.size == 1 do
      return Except.error (StepError.invalidProgram "non-enum ADT has invalid variant declarations")
    let fields := declaration.fields.filter (fun field => field.variantIndex == 0 && field.fieldName == name)
    unless fields.size == 1 do
      return Except.error (StepError.invalidProgram s!"missing or ambiguous compiler field {name}")
    let some field := fields[0]? | return Except.error (StepError.invalidProgram "missing named field")
    pure (Except.ok field.fieldIndex)
  match result with | .ok index => pure index | .error error => throw error

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
