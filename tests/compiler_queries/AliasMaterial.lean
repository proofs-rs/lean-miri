import Miri.Input.AliasMaterialCodec
import Miri.Input.AliasMaterialProgram

open Lean Miri.Input
private def must (value : Except String A) : IO A :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
private def read (text : String) : Except String AliasMaterial.Declaration := do
  AliasMaterialCodec.readDeclaration (← Json.parse text)

def main : IO Unit := do
  let free ← must (read "{\"definition\":{\"crate\":0,\"index\":1},\"kind\":\"free\",\"is_checked\":true,\"has_value\":true}")
  let rhs : GenericSubstitution.DefinitionTemplate := {
    parameters := #[], typeExpression := .atom .type "bool" "", signatureExpression := none, fields := #[] }
  let program ← must (AliasMaterial.program #[(free,some rhs)])
  check (program.freeRules.size == 1) "raw free RHS was not shared into program"
  let ordinary := {free with kind := .free false}
  let eager ← must (AliasMaterial.program #[(ordinary,some rhs)])
  check (eager.freeRules.isEmpty) "ordinary warning-only alias bounds became enforced free-alias goals"
  check (!(AliasMaterial.program #[(free,none)]).isOk) "missing RHS became empty normalization"
  check (!(AliasMaterial.program #[(free,some rhs),(free,some rhs)]).isOk) "duplicate raw alias declaration accepted"
  let abstract ← must (read "{\"definition\":{\"crate\":0,\"index\":2},\"kind\":\"associated\",\"container\":\"trait\",\"parent\":{\"crate\":0,\"index\":10},\"parent_parameter_count\":1,\"is_final\":false,\"has_value\":false}")
  let program ← must (AliasMaterial.program #[(abstract,none)])
  check (program.associatedDeclarations.size == 1 && program.freeRules.isEmpty)
    "abstract associated declaration became an RHS answer"
  check (!(AliasMaterial.rule abstract none).isOk) "abstract associated RHS accepted"
  for invalid in [
    "{\"definition\":{\"crate\":0,\"index\":1},\"kind\":\"free\",\"is_checked\":true}",
    "{\"definition\":{\"crate\":0,\"index\":1},\"kind\":\"free\",\"is_checked\":true,\"has_value\":true,\"own_predicates\":[],\"normalized\":0}",
    "{\"definition\":{\"crate\":0,\"index\":1},\"kind\":\"free\",\"is_checked\":true,\"has_value\":true,\"own_predicates\":[{\"variables\":[],\"predicate\":{\"kind\":\"imaginary\"}}]}" ] do
    check (!(read invalid).isOk) "source alias reader dropped missing/unknown obligation material"
  IO.println "raw alias declarations: shared RHS, abstract defaults, duplicate/missing/unknown material checks passed"
