import Miri.Input.Decoder
import Miri.Input.RuntimeArrayTypes

/-! A coroutine can need a frame/layout before any resume-body demand. The
producer must retain one raw declaration per physical owner on type discovery;
repeated closed instantiations cannot replace it with layout or body answers. -/
open Miri.Input Miri.Input.TypeArena
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

def main (args : List String) : IO Unit := do
  let [input] := args | throw (IO.userError "expected actual no-resume input")
  let document := (← must (decodeJson (← IO.FS.readFile input))).document
  let runtime ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let some coverage := document.coroutineCoverage | throw (IO.userError "coroutine source catalog absent")
  unless coverage.coroutines.isEmpty && coverage.auxiliaryBodies.isEmpty &&
      coverage.bodyCoroutines.all (· == false) && coverage.genericSources.size == 1 do
    throw (IO.userError "type-only coroutine discovery fabricated bodies or duplicated its raw source")
  let material ← must (World.ofMaterial document.types document.typeConstants document.definitions document.predicates runtime.target.pointerSize.bytes.toNat)
  let nodes := document.types.filter (·.shapeKind == .coroutine)
  unless nodes.size == 2 do throw (IO.userError "no-resume fixture lost repeated-u8/distinct-u64 identities")
  for node in nodes do
    let term ← must (GenericInstantiationWorld.ofType material 16384 node.id)
    let empty ← must (World.ofMaterial #[] #[] document.definitions document.predicates runtime.target.pointerSize.bytes.toNat)
    let (id,world) ← must ((GenericInstantiationWorld.resolveType 16384 term).run empty)
    let (actual,_) ← must ((RuntimeMetadata.layoutInWorld runtime id).run world)
    let expected ← must ((runtime.layoutById node.layoutId).mapError toString)
    unless actual.layout == expected do throw (IO.userError "type-only raw coroutine layout differs from complete compiler layout")
    let missing := {runtime with source := {runtime.source with
      coroutineCoverage := some {coverage with genericSources := #[]}}}
    -- Both material and constructed identities must reject missing raw source,
    -- even though their compiler physical layout answers remain available.
    for (candidate,world) in [(id,world),(node.id,material)] do
      match (RuntimeMetadata.layoutInWorld missing candidate).run world with
      | .error "coroutine source instantiation: ordinary owner missing or ambiguous" => pure ()
      | .error error => throw (IO.userError s!"wrong absent raw-source rejection: {error}")
      | .ok _ => throw (IO.userError "coroutine layout copied a compiler answer when raw source was missing")
  IO.println "PASS two type-only coroutine layouts, repeated source reuse, no fabricated resume/auxiliary bodies and missing-source rejection"
