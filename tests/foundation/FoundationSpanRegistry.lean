import Miri.Frontend.FoundationSpanRegistry
open Lean Miri.Frontend.Foundation

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "expected fresh foundation JSON path")
  let contents ← IO.FS.readFile path
  let checked := do
    let document ← Json.parse contents
    let bodies ← document.getObjValAs? (Array Json) "bodies"
    for body in bodies do
      let registry ← buildSpanRegistry body
      let (withRoot, rootId) ← appendSessionRootSpan registry document
      unless (withRoot.spans[rootId]?).any (fun (entry : Miri.Input.SourceSpanData) => entry.isDummy) do throw "missing session root span"
      unless registry.spans.size == registry.compilerSpans.size do throw "span registry lost identity"
      let metadata ← body.getObjVal? "source_metadata"
      let scopes ← metadata.getObjValAs? (Array Json) "scopes"
      let some original := scopes[0]? | throw "missing source scope"
      let originalSpan ← original.getObjVal? "span"
      let originalId ← originalSpan.getObjValAs? Nat "span_id"
      let distinct := originalSpan.setObjVal! "span_id" (toJson registry.spans.size)
      let scope := Json.mkObj [("span", distinct), ("parent", toJson (0 : Nat)), ("inlined_parent", Json.null)]
      let changed := body.setObjVal! "source_metadata"
        (metadata.setObjVal! "scopes" (toJson (scopes.push scope)))
      let extended ← buildSpanRegistry changed
      unless extended.spans.size == registry.spans.size + 1 do throw "distinct compiler identity collapsed"
      unless extended.spans[registry.spans.size]? == registry.spans[originalId]? do
        throw "diagnostically equal physical span payload changed"
      for entry in registry.backtraces do
        unless entry.spanId < registry.spans.size && entry.position.filename < registry.files.size do
          throw "backtrace relocation invalid"
  match checked with
  | .ok () => IO.println "fresh exact compiler span registry passed"
  | .error e => throw (IO.userError e)
