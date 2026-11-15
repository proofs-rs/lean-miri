import Miri.Input.SourceCompilerWorld
import Miri.Input.Decoder
open Miri Miri.Input Miri.Input.SourceCompilerWorld Miri.Interpreter
private def expect (r : Except String α) : IO α := match r with
| .ok a => pure a | .error e => throw (IO.userError e)
private def check (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)
private def rejects (r : Except String α) : IO Unit := match r with
| .error _ => pure () | .ok _ => throw (IO.userError "invalid source identity accepted")
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "usage: schema12-reference")
  let document := (← expect (decodeJson (← IO.FS.readFile path))).document
  let seeded ← expect (create document)
  let some first := document.instances[0]? | throw (IO.userError "compiler seed absent")
  let firstKey ← expect (keyOf seeded first.id)
  let (same,id) ← expect (internItem #[] seeded firstKey)
  check (id == first.id && same.canonical.instances.size == document.instances.size) "imported identity was renumbered"
  let rootBody ← expect (bodyId seeded first.id)
  check (first.bodyId == some rootBody) "imported body capability changed"
  let some second := document.instances.find? (fun node =>
    node.instanceKind != first.instanceKind && node.genericArgs.isEmpty &&
      match node.instanceKind with | .Item _ => true | _ => false)
    | throw (IO.userError "second genuine compiler Item absent")
  let secondKey ← expect (keyOf seeded second.id)
  check (firstKey.arguments.isEmpty && secondKey.arguments.isEmpty) "fixture keys unexpectedly generic"
  let declarations : Array ItemDeclaration := #[
    ⟨firstKey.definition, first.defPath.getD "", .function, #[]⟩,
    ⟨secondKey.definition, second.defPath.getD "", .function, #[]⟩]
  -- The identity-only view retains real source definitions/types, with no
  -- instantiated MIR/ABI capabilities. It is not an executable test Program.
  let initial ← expect (create {document with instances := #[], bodies := #[], bodyRoots := #[]})
  check (initial.canonical.instances.isEmpty) "declarations eagerly minted identities"
  let (one,a) ← expect (internItem declarations initial firstKey)
  let (two,b) ← expect (internItem declarations one secondKey)
  let (again,a') ← expect (internItem declarations two firstKey)
  check (a == 0 && b == 1 && a' == a && again.canonical.instances.size == 2) "demand-only canonical interning/dedup"
  check ((← expect (keyOf again a)) == firstKey && (← expect (keyOf again b)) == secondKey) "full key roundtrip"
  let actual ← expect (node again a)
  check (actual.kind == .identityOnly && actual.bodyId.isNone) "identity fabricated MIR capability"
  rejects (bodyId again a)
  rejects (internItem #[] initial firstKey)
  let some duplicate := declarations[0]? | throw (IO.userError "declaration missing")
  rejects (internItem (declarations.push duplicate) initial firstKey)
  rejects (internItem declarations initial {firstKey with arguments := #[.Lifetime .Erased]})
  rejects (internItem declarations initial ⟨⟨0,2^32⟩,#[]⟩)
  rejects (node again 2)
  rejects (create {document with definitions := document.definitions.push firstKey.definition})
  rejects (create {document with instances := document.instances.push {first with id := document.instances.size}})
  IO.println "PASS persistent demanded Item identities, imported handles, exact dedup and capability/duplicate/argument rejection"
#print axioms Miri.Input.SourceCompilerWorld.internItem_existing
