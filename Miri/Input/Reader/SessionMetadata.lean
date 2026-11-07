import Miri.Input.Reader.RuntimeQueries

namespace Miri.Input.Reader.SessionMetadataReader
open Lean

/-- Resolve catalog references at the reader boundary; compiler consumers retain
only typed session and crate metadata. Failures remain demanded queries. -/
def session (catalog : Catalog) : Except String SessionMetadataData := do
  let path := "$.compiler_session_queries"
  let source ← catalog.field catalog.root "compiler_session_queries" "$"
  let features := do
    (← catalog.array (← catalog.field source "internal_target_features" path) path).mapM
      fun value => catalog.string value path
  let wasm := do catalog.boolean (← catalog.field source "is_like_wasm" path) path
  let checks := do
    let mut checks : Array (Miri.MIR.RuntimeChecks × Bool) := #[]
    for check in ← catalog.array (← catalog.field source "runtime_checks" path) path do
      unless (← catalog.string (← catalog.field check "status" path) path) == "supported" do
        throw "compiler session runtime-check query unavailable"
      let kind ← catalog.string (← catalog.field check "kind" path) path
      let kind : Miri.MIR.RuntimeChecks ← match kind with
        | "ub_checks" => pure .UbChecks
        | "contract_checks" => pure .ContractChecks
        | "overflow_checks" => pure .OverflowChecks
        | _ => throw "unknown compiler runtime-check kind"
      unless !(checks.any (·.1 == kind)) do throw "duplicate compiler runtime-check query"
      checks := checks.push (kind,← catalog.boolean (← catalog.field check "enabled" path) path)
    return checks
  let arch := do catalog.string (← catalog.field source "target_arch" path) path
  return ⟨features,wasm,checks,arch⟩

def frame (catalog : Catalog) : Except String FrameMetadataData := do
  let path := "$.compiler_frame_metadata"
  let source ← catalog.field catalog.root "compiler_frame_metadata" "$"
  let localId ← catalog.natural (← catalog.field source "local_crate" path) path
  let mut crates := #[]
  for entry in ← catalog.array (← catalog.field source "crates" path) path do
    let id ← catalog.natural (← catalog.field entry "crate" path) path
    let name ← catalog.string (← catalog.field entry "name" path) path
    if crates.any (·.1 == id) then throw "duplicate compiler crate identity"
    crates := crates.push (id,name)
  unless crates.any (·.1 == localId) do throw "local compiler crate name absent"
  return ⟨localId,crates⟩

end Miri.Input.Reader.SessionMetadataReader
