import Miri.Input.RuntimeProgram
import Lean.Util.Profile
import Miri.Input.CompilerInstance
import Miri.Input.RuntimeMetadata
import Miri.Interpreter.Constant

namespace Miri.Input.CompilerConstantQueries
open Lean Miri.Interpreter

structure Site where
  bodyIndex : Nat
  constantId : MIR.ConstantId
  deriving Repr, DecidableEq

structure Prepared where
  owner : RuntimeProgram
  bodies : Array (Except String (MIR.SharedTable (Except String CompilerConstantEvidence)))
  obligations : Array Obligation

@[inline] def Prepared.program (prepared : Prepared) : LoweredProgram := prepared.owner.program
@[inline] def Prepared.runtime (prepared : Prepared) : RuntimeMetadata := prepared.owner.runtime

def Prepared.withProgram (prepared : Prepared) (program : LoweredProgram) : Prepared :=
  {prepared with owner := prepared.owner.withProgram program}

def prepareProfiled (_profile : Lean.Options) (owner : RuntimeProgram) : Except String Prepared := do
  let program := owner.program
  let tables := program.input.mirTables
  let mut bodies := #[]
  let mut obligations := #[]
  for bodyIndex in [:program.bundle.bodies.size] do
    let context := do
      let some source := tables.bodySources[bodyIndex]? | throw "body compiler instance absent"
      let callee ← source.callee
      let some result := tables.normalization[bodyIndex]? | throw "body normalization metadata absent"
      return (callee,← result)
    match context with
    | .error reason =>
      bodies := bodies.push (.error reason)
      obligations := obligations.push ⟨s!"bodies[{bodyIndex}].constant_query_context",reason⟩
    | .ok (callee,mapping) =>
      let mut constants := Array.replicate tables.mir.constants.size none
      for (sourceId,normalizedId) in mapping.constants do
        let query := do
          let source ← tables.mir.constants.lookup sourceId.index |>.mapError (fun id => s!"invalid source constant {id}")
          let normalized ← tables.mir.constants.lookup normalizedId.index |>.mapError (fun id => s!"invalid normalized constant {id}")
          return (⟨callee,source.operand.value,normalized.operand.value,normalized.operand.span,← normalized.evaluation⟩ : CompilerConstantEvidence)
        if let .error reason := query then
          obligations := obligations.push ⟨s!"bodies[{bodyIndex}].constant[{sourceId.index}]",reason⟩
        if bound : sourceId.index < constants.size then
          constants := constants.set sourceId.index (some query) bound
        else throw "source constant ID outside table"
      bodies := bodies.push (.ok constants)
  return ⟨owner,bodies,obligations⟩

def prepare (owner : RuntimeProgram) : Except String Prepared :=
  prepareProfiled {} owner

def lookup (prepared : Prepared) (site : Site) : Except String CompilerConstantEvidence := do
  let some body := prepared.bodies[site.bodyIndex]? | throw "constant body identity absent"
  let query ← (← body).lookup site.constantId.index |>.mapError (fun id => s!"constant {id} has no compiler normalization evidence in this body")
  query


end Miri.Input.CompilerConstantQueries
