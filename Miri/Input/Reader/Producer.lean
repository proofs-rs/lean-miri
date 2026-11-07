import Miri.Input.Reader.Catalog
import Miri.Input.Model.Types

namespace Miri.Input.Reader

def Catalog.producer (catalog : Catalog) : Except String Producer := do
  let value ← catalog.field catalog.root "producer" "$"
  let text key := do
    catalog.string (← catalog.field value key "$.producer") s!"$.producer.{key}"
  return {
    miriCommit := ← text "miri_commit"
    rustcCommit := ← text "rustc_commit"
    rustcVersion := ← text "rustc_version"
    targetTriple := ← text "target_triple" }

end Miri.Input.Reader
