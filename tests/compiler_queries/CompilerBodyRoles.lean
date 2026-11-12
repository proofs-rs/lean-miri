import Miri.Input.Decoder
import Miri.Input.SourceMir
open Miri.Input
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fresh raw-template source fixture")
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let types ← must (TypeArena.World.ofDocument document)
  let instances ← must (InstanceArena.Store.ofSource types document.instances)
  let some (.copyTemplate reference) := document.bodies.find? (fun body => match body with
      | .copyTemplate _ => true | _ => false)
    | throw (IO.userError "genuine raw template body missing")
  let some source := document.mirTemplates[reference.templateId]?
    | throw (IO.userError "raw source template missing")
  check (source.sourceRole == .runtime) "producer runtime source has wrong role"
  let templates := #[source,{source with sourceRole := .ctfe}]
  let runtime ← must (BodyArena.Key.create types instances templates 0 reference.instanceId source.sourcePromoted .runtime)
  let ctfe ← must (BodyArena.Key.create types instances templates 1 reference.instanceId source.sourcePromoted .ctfe)
  check (runtime.instanceKey == ctfe.instanceKey && runtime.promoted == ctfe.promoted)
    "role test changed physical instance or promoted identity"
  check (runtime != {runtime with role := .ctfe}) "body key discarded compiler source role"
  check (!(BodyArena.Key.create types instances templates 0 reference.instanceId source.sourcePromoted .ctfe).isOk)
    "CTFE request accepted runtime template source"
  let store := BodyArena.Store.ofSource #[]
  let (runtimeId,store) ← must (store.intern types instances templates #[] runtime)
  let (ctfeId,store) ← must (store.intern types instances templates #[] ctfe)
  check (runtimeId == 0 && ctfeId == 1 && store.constructed.size == 2)
    "same-instance same-promoted source roles collapsed in the body arena"
  check (!(store.intern types instances templates #[] {runtime with role := .ctfe}).isOk)
    "forged role/source contradiction was interned"
  let document := {document with mirTemplates := document.mirTemplates.set! reference.templateId {source with sourceRole := .ctfe}}
  let some index := document.bodies.findIdx? (fun body => match body with
      | .copyTemplate value => value.templateId == reference.templateId | _ => false)
    | throw (IO.userError "template reference missing")
  check (!((SourceMir.resolveBody document index .runtime).run types).isOk)
    "runtime source resolution consumed CTFE role"
  let some materialIndex := document.bodies.findIdx? (fun body => match body with
      | .material _ => true | _ => false)
    | throw (IO.userError "genuine material body missing")
  let some (.material material) := document.bodies[materialIndex]?
    | throw (IO.userError "material body lookup changed")
  let changed := {document with bodies := document.bodies.set! materialIndex (.material {material with sourceRole := .ctfe})}
  check (!((SourceMir.resolveBody changed materialIndex .runtime).run types).isOk)
    "runtime source resolution consumed a CTFE material body"
  IO.println "PASS compiler body role keys, exact instance/promoted separation and runtime/source-mix rejection"
