import Miri.ABI.CoroutineLayout
import Miri.ABI.UnivariantLayout
import Miri.Input.Decoder
import Miri.Input.RuntimeMetadata

/-! Pinned rustc_abi/src/layout/coroutine.rs. Inputs are saved-local child
layouts, upvar child layouts and raw transformed-MIR field/conflict relations.
The caller separately instantiates MaybeUninit<T> local types and applies the
physical definition hash seed as rustc_ty_utils::layout does. -/


open Lean Miri.ABI Miri.Input
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def physical (target : RuntimeTargetDataLayout) (row : Json) : IO LayoutData := do
  let source ← must (JsonReader.run DecoderValues.parseLayout row.compress)
  must ((RuntimeMetadata.layout target source).mapError toString)
private def indices (row : Json) : IO (Array (Array Nat)) := do
  (← must row.getArr?).mapM fun row => must (row.getArr? >>= Array.mapM Json.getNat?)
def main (args : List String) : IO Unit := do
  let [targetPath, oraclePath] := args | throw (IO.userError "usage: CoroutineLayoutCalculator TARGET_DOCUMENT ORACLE")
  let raw ← must (Json.parse (← IO.FS.readFile targetPath))
  let sourceTarget ← must (JsonReader.run CatalogDecoder.targetDataLayout
    (← must (raw.getObjVal? "runtime_target_data_layout")).compress)
  let target ← must ((RuntimeMetadata.importTarget sourceTarget).mapError toString)
  let rows ← must ((← must (Json.parse (← IO.FS.readFile oraclePath))).getArr?)
  for row in rows do
    let name ← must ((← must (row.getObjVal? "name")).getStr?)
    let locals ← (← must ((← must (row.getObjVal? "locals")).getArr?)).mapM (physical target)
    let upvars ← (← must ((← must (row.getObjVal? "prefix")).getArr?)).mapM (physical target)
    let variants ← indices (← must (row.getObjVal? "variants"))
    let conflicts ← indices (← must (row.getObjVal? "conflicts"))
    let expected ← physical target (← must (row.getObjVal? "layout"))
    let actual ← must (CoroutineLayout.compute target locals upvars variants conflicts)
    unless actual == expected do throw (IO.userError s!"complete coroutine layout differs from pinned rustc: {name}")
  IO.println s!"PASS {rows.size} complete coroutine calculator layouts against actual pinned rustc"
