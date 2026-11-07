import Miri.Input.Reader.Table
import Miri.Input.Model.Types

namespace Miri.Input.Reader
open Lean Miri.MIR

private def position (catalog : Catalog) (input : Json) (path : String) :
    Except String SourcePosition := do
  return {
    line := ← catalog.natural (← catalog.field input "line" path) s!"{path}.line"
    column := ← catalog.natural (← catalog.field input "column" path) s!"{path}.column" }

private def diagnostic (catalog : Catalog) (input : Json) (path : String) :
    Except String String := do
  let value ← catalog.inspect input path
  let status ← catalog.string (← catalog.field value "status" path) s!"{path}.status"
  unless status == "debug_payload" do throw s!"{path}: expected diagnostic payload"
  catalog.string (← catalog.field value "rustc_debug" path) s!"{path}.rustc_debug"

def Catalog.decodeSourceSpan (catalog : Catalog) (input : Json) (path : String) :
    Except String SourceSpanData := do
  return {
    lo := ← catalog.natural (← catalog.field input "lo" path) s!"{path}.lo"
    hi := ← catalog.natural (← catalog.field input "hi" path) s!"{path}.hi"
    start := ← position catalog (← catalog.field input "start" path) s!"{path}.start"
    «end» := ← position catalog (← catalog.field input "end" path) s!"{path}.end"
    context := ← diagnostic catalog (← catalog.field input "ctxt" path) s!"{path}.ctxt"
    file := ← diagnostic catalog (← catalog.field input "file" path) s!"{path}.file" }

def Catalog.readSourceSpan (catalog : Catalog) (table : SharedTable SourceSpanData)
    (input : Json) (path : String) : Except String (Nat × SharedTable SourceSpanData) :=
  catalog.readEntry table (fun value => catalog.decodeSourceSpan value path) input path

end Miri.Input.Reader
