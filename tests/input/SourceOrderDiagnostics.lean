import Miri.Input.Decoder

open Lean Miri.Input
private def must {α} (x : Except String α) : IO α :=
  match x with | .ok a => pure a | .error e => throw (IO.userError e)
private def check (x : Bool) (e : String) : IO Unit :=
  unless x do throw (IO.userError e)
private def set (catalog : Reader.Catalog) (j : Json) (key : String) (value : Json) : Except String Json := do
  let .obj fields ← catalog.inspect j "test" | throw "expected test object"
  return Json.mkObj ((key,value) :: fields.toList.filter (fun row => row.1 != key))
private def field (c : Reader.Catalog) (j : Json) (key : String) := c.field j key "test"
private def probes (c : Reader.Catalog) : Except String (Array (Nat × Nat × String)) := do
  let instanceRows ← c.array (← field c c.sourceRoot "instances") "instances"
  let mut result := #[]
  for (entry,i) in instanceRows.toList.zipIdx do
    let some body := (field c entry "body").toOption | continue
    let some blocks := ((field c body "basic_blocks").bind (fun j => c.array j "blocks")).toOption | continue
    for (block,b) in blocks.toList.zipIdx do
      let statements ← c.array (← field c block "statements") "statements"
      for s in [:statements.size] do
        let path := s!"instances[{i}].body.basic_blocks[{b}].statements[{s}].kind.rvalue.vtable_probe"
        if @exactVtableProbeDiagnostic c.jsonFields c.sourceRoot ("$." ++ path ++ ".status") then
          let id ← c.natural (← field c entry "instance_id") "instance_id"
          result := result.push (i,id,path)
  return result
private def rebase (path : String) (a b : Nat) : String :=
  let x := s!"instances[{a}]"
  let y := s!"instances[{b}]"
  if path.startsWith x then y ++ (path.drop x.length).toString
  else if path.startsWith y then x ++ (path.drop y.length).toString
  else path

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "expected rooted vtable fixture")
  let input ← must (Json.parse (← IO.FS.readFile path))
  let c ← must (Reader.Catalog.parse input)
  let some (sourceIndex,id,probe) := (← must (probes c))[0]? | throw (IO.userError "fixture lacks validated probe")
  let target := if id == 0 then 1 else 0
  let rows ← must (c.array (← must (field c c.sourceRoot "instances")) "instances")
  let some a := rows[sourceIndex]? | throw (IO.userError "source row absent")
  let some b := rows[target]? | throw (IO.userError "target row absent")
  let rows ← if ha : sourceIndex < rows.size then
    if hb : target < rows.size then pure ((rows.set sourceIndex b ha).set target a (by simpa using hb))
    else throw (IO.userError "target outside array")
    else throw (IO.userError "source outside array")
  let scope ← must (field c c.sourceRoot "selected_scope")
  let records ← must (c.array (← must (field c scope "retained_catalog_obligations")) "retained")
  let records ← records.mapM fun row => do
    let old ← must (c.string (← must (field c row "path")) "path")
    must (set c row "path" (.str (rebase old sourceIndex target)))
  let newProbe := rebase probe sourceIndex target
  let marker := Json.mkObj [("kind",.str "symbolic_vtable_allocation"),("status",.str "incomplete"),
    ("diagnostic_only",.bool true),("path",.str newProbe),("reason",.str "source-order regression marker")]
  let markerPath := s!"$.selected_scope.retained_catalog_obligations[{records.size}].status"
  let scope ← must (set c scope "retained_catalog_obligations" (.arr (records.push marker)))
  let root ← must (set c c.sourceRoot "instances" (.arr rows))
  let root ← must (set c root "selected_scope" scope)
  let root ← must (set c root "shared_payloads" (Json.mkObj [
    ("schema_version",toJson (2 : Nat)),("nodes",.arr c.nodes)]))
  let current ← must (decodeRuntimeJson root.compress)
  check (current.document.obligations.any (·.path == markerPath)) "source diagnostic was erased"
  check (!(current.blockingObligations.any (·.path == markerPath))) "source-order diagnostic misclassified as structural"
  let reordered ← must (Reader.Catalog.parse root)
  check (@exactVtableProbeDiagnostic reordered.jsonFields reordered.sourceRoot ("$." ++ newProbe ++ ".status"))
    "transport order no longer identifies the original validated probe"
  check (target != id) "test did not distinguish source order from ID order"
  -- A forged producer hint still blocks: diagnostic_only is not sufficient.
  let spoof := Json.mkObj [("kind",.str "symbolic_vtable_allocation"),("status",.str "incomplete"),
    ("diagnostic_only",.bool true),("path",.str (newProbe ++ ".missing"))]
  let scope ← must (set c scope "retained_catalog_obligations" (.arr (records.push spoof)))
  let root ← must (set c root "selected_scope" scope)
  let rejected ← must (decodeRuntimeJson root.compress)
  check (rejected.blockingObligations.any (·.path == markerPath)) "forged source hint erased a structural blocker"
  IO.println "producer source-order diagnostics survive ID indexing; forged hints remain blocking: PASS"
