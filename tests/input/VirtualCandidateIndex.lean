import Miri.Input.SharedPayloads
import Miri.Input.CompilerVirtualCandidates

/-! Finite transport/join checks on a fresh compiler export. This does not
execute guest MIR or claim source-program safety. -/
open Lean Miri.Input

private def must {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def replaceField (source : Json) (name : String) (value : Json) : Except String Json := do
  let fields ← source.getObj?
  return Json.mkObj ((name, value) :: fields.toList.filter (·.1 != name))

def main (args : List String) : IO Unit := do
  let path ← match args with
    | path :: _ => pure path
    | [] => throw (IO.userError "usage: VirtualCandidateIndex <fresh virtual export>")
  let raw ← must (Json.parse (← IO.FS.readFile path))
  let document ← must (SharedPayloads.resolveCatalog raw)
  let source ← must (document.getObjVal? "compiler_virtual_candidates")
  let instances ← must ((document.getObjVal? "instances").bind Json.getArr?)
  let queries ← must ((document.getObjVal? "compiler_vtable_queries").bind Json.getArr?)
  let virtuals ← must ((document.getObjVal? "compiler_runtime_queries").bind fun runtime =>
    (runtime.getObjVal? "virtual").bind Json.getArr?)
  check (!virtuals.isEmpty) "fixture has no virtual compiler-query rows"
  let catalog := CompilerVirtualCandidates.ofJson source
  let mut checked := 0
  for query in virtuals do
    let instanceId ← must (query.getObjValAs? Nat "original_instance_id")
    let reference ← must (query.getObjVal? "vtable_query")
    let _ ← must (catalog.query instanceId instances.size queries reference)
    checked := checked + 1
    -- Missing evidence and an explicitly empty candidate set must both reject
    -- this actual compiler query, while remaining distinct index states.
    let slots ← must ((source.getObjVal? "by_instance").bind Json.getArr?)
    let missing ← must (replaceField source "by_instance" (.arr (slots.set! instanceId .null)))
    let empty ← must (replaceField source "by_instance" (.arr (slots.set! instanceId (.arr #[]))))
    check (!((CompilerVirtualCandidates.ofJson missing).query instanceId instances.size queries reference).isOk)
      "missing candidate slot accepted an actual virtual query"
    check (!((CompilerVirtualCandidates.ofJson empty).query instanceId instances.size queries reference).isOk)
      "empty candidate set accepted an actual virtual query"
  IO.println s!"virtual candidate index: {checked} exact compiler-query joins; missing/empty controls rejected"
