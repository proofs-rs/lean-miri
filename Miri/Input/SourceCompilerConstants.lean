import Miri.Input.SourceFunctionTypes
import Miri.Input.Model.SourceConstValues

/-! Exact demand lookup of concrete compiler-evaluated constants. Compiler CTFE
and faithful witness capture are trusted inputs; Lean performs substitution and
identity matching, not generic const evaluation or trait/default selection. -/
namespace Miri.Input.SourceCompilerConstants
open SourceTypes
abbrev World := SourceCompilerWorld.World

private def typeReference (world : World) (reference : Nat)
    (types : Array (Option Concrete)) (constants : Array (Option Nat)) :
    Except String (World × Nat) := do
  let some source := world.canonical.sourceMaterial | throw "constant source material unavailable"
  let some physical := source.physical | throw "constant source types unavailable"
  match physical.types[reference]? with
  | some (.functionDefinition ..) => SourceFunctionTypes.internSource world reference types constants
  | _ => SourceSignatureTypes.intern world types constants #[] reference

private def arguments (initial : World) (values : Array Argument)
    (caller : Array MIR.GenericArg) (types : Array (Option Concrete))
    (constants : Array (Option Nat)) : Except String (World × Array MIR.GenericArg) := do
  let some source := initial.canonical.sourceMaterial | throw "constant source material unavailable"
  let some physical := source.physical | throw "constant source types unavailable"
  let mut world := initial
  let mut result := #[]
  for value in values do
    match value with
    | .type reference =>
      if let some (.parameter index _) := physical.types[reference]? then
        let some (.Type id) := caller[index]? | throw "constant type argument parameter unavailable"
        result := result.push (.Type id)
      else
        let (updated,id) ← typeReference world reference types constants
        world := updated
        result := result.push (.Type id)
    | .constant (.parameter index _) =>
      let some (.Const id) := caller[index]? | throw "constant value argument parameter unavailable"
      result := result.push (.Const id)
    | .constant (.value reference bits bytes) =>
      let (updated,type) ← typeReference world reference types constants
      let (updated,id) ← SourceCompilerWorld.internScalarConstant updated type bits bytes
      world := updated
      result := result.push (.Const id)
    | .lifetime .static => result := result.push (.Lifetime .Static)
    | .lifetime .erased => result := result.push (.Lifetime .Erased)
    | .lifetime (.earlyParameter index) =>
      let some (.Lifetime region) := caller[index]? | throw "constant region argument parameter unavailable"
      result := result.push (.Lifetime region)
    | _ => throw "Unsupported constant generic argument syntax"
  return (world,result)

/-- Consume a retained generic token only when its full concrete key has a
compiler result in this source document. Missing coverage remains Unsupported.
Source allocation identities are not synthesized; this first value domain is
scalar or zero-sized. -/
def demand (initial : World) (request : SourceCompilerWorld.ConstantRequest) :
    Except String (World × Nat × SourceMir.ConstantValue) := do
  let some source := initial.canonical.sourceMaterial | throw "constant source material unavailable"
  let some physical := source.physical | throw "constant source types unavailable"
  let some material := source.constantValues | throw "concrete compiler constant results unavailable"
  let some definition := physical.definitions[request.definition]? | throw "constant source definition unavailable"
  let (world,key) ← arguments initial request.arguments request.callerArguments request.types request.constants
  let mut world := world
  let mut selected : Option SourceConstValues.Row := none
  for row in material.rows do
    if row.definition != definition.raw || row.promoted != request.promoted then continue
    let (updated,candidate) ← arguments world row.arguments #[] #[] #[]
    world := updated
    if candidate != key then continue
    unless selected.isNone do throw "concrete compiler constant result key ambiguous"
    selected := some row
  let some row := selected | throw "concrete compiler constant result key unavailable"
  let (finalWorld,type) ← match physical.types[row.typeRef]? with
    | some (.functionDefinition ..) => SourceFunctionTypes.internSource world row.typeRef #[] #[]
    | _ => do
      let concrete ← SourceTypes.instantiate physical #[] #[] row.typeRef >>= SourceTypes.eraseRegions
      SourcePhysical.intern world concrete
  unless type == request.expectedType do throw "concrete compiler constant result type mismatch"
  let value := match row.value with
    | .scalar bits bytes => SourceMir.ConstantValue.scalar bits bytes
    | .zeroSized => .zeroSized
  return (finalWorld,type,value)
end Miri.Input.SourceCompilerConstants
