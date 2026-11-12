import Miri.Input.Decoder
import Miri.Input.CompilerScopes
import Miri.Input.CompilerLifecycle
import Miri.Input.CompilerBacktraceSource
import Miri.Input.CallResolution

/-! Demand-order regression, not a guest safety comparison. An unresolved
source type expression must not be evaluated while preparing body metadata;
requesting that actual executable body must reject rather than produce MIR. -/
open Lean Miri.Input
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error e => throw (IO.userError e)
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fresh input containing a source MIR template")
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let document := decoded.document
  let some index := document.bodies.findIdx? (fun seed => match seed with
    | .copyTemplate _ => true | .material _ => false)
    | throw (IO.userError "fresh input contains no body-template references")
  let some (.copyTemplate reference) := document.bodies[index]?
    | throw (IO.userError "body-template reference disappeared")
  let some source := document.mirTemplates[reference.templateId]?
    | throw (IO.userError "body-template source disappeared")
  check (!source.template.types.isEmpty) "source template has no type expressions"
  let blocked := {source with template := {source.template with
    types := source.template.types.map fun _ =>
      GenericSubstitution.Term.atom .type "unavailable_body_type_test" ""}}
  let blockedDocument := {document with
    mirTemplates := document.mirTemplates.set! reference.templateId blocked}
  let program ← must (lowerProgram blockedDocument)
  check (program.bodyCount == document.bodies.size) "preparation changed canonical body identities"
  let _ ← must (CallResolution.prepare program)
  let scopes ← must (CompilerScopes.prepare program)
  let lifecycle := CompilerLifecycle.prepare scopes.program
  let _ ← must (CompilerBacktraceSource.prepare lifecycle.program)
  match program.resolveBody index with
  | .ok _ => throw (IO.userError "unresolved template unexpectedly supplied executable MIR")
  | .error _ => pure ()
  IO.println "PASS source body metadata stays lazy; unresolved actual-body demand rejects"
