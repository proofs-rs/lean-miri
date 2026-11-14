import Miri.ABI.MaybeUninitLayout
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
  let [targetPath, oraclePath] := args | throw (IO.userError "usage: CoroutineMaybeUninit TARGET_DOCUMENT ORACLE")
  let raw ← must (Json.parse (← IO.FS.readFile targetPath))
  let sourceTarget ← must (JsonReader.run CatalogDecoder.targetDataLayout
    (← must (raw.getObjVal? "runtime_target_data_layout")).compress)
  let target ← must ((RuntimeMetadata.importTarget sourceTarget).mapError toString)
  let rows ← must ((← must (Json.parse (← IO.FS.readFile oraclePath))).getArr?)
  let mut checks := 0
  for row in rows do
    for sample in ← must ((← must (row.getObjVal? "oracle")).getArr?) do
      let values ← must ((← must (sample.getObjVal? "saved_layouts")).getArr?)
      let wrappers ← must ((← must (sample.getObjVal? "wrapper_source")).getArr?)
      let expected ← must ((← must (sample.getObjVal? "locals")).getArr?)
      unless values.size == wrappers.size && values.size == expected.size do throw (IO.userError "wrapper domain mismatch")
      for i in [:values.size] do
        let some value := values[i]? | throw (IO.userError "value absent")
        let some wrapper := wrappers[i]? | throw (IO.userError "wrapper absent")
        let some answer := expected[i]? | throw (IO.userError "answer absent")
        let number (key : String) : IO UInt64 := do
          pure (UInt64.ofNat (← must ((← must (wrapper.getObjVal? key)).getNat?)))
        let manuallyDrop : UnivariantLayout.Representation := {
          flags := UInt8.ofNat (← number "manually_drop_flags").toNat
          fieldShuffleSeed := ← number "manually_drop_seed" }
        let maybeUninit : UnivariantLayout.Representation := {
          flags := UInt8.ofNat (← number "maybe_uninit_flags").toNat
          fieldShuffleSeed := ← number "maybe_uninit_seed" }
        let actual ← must (MaybeUninitLayout.compute target (← physical target value) manuallyDrop maybeUninit)
        unless actual == (← physical target answer) do throw (IO.userError s!"complete MaybeUninit layout differs actual={repr actual} expected={repr (← physical target answer)}")
        unless (MaybeUninitLayout.compute target (← physical target value) {manuallyDrop with flags := 0} maybeUninit).toOption.isNone do
          throw (IO.userError "malformed ManuallyDrop source accepted")
        checks := checks + 1
  IO.println s!"PASS {checks} complete MaybeUninit wrappers from raw ADT repr + saved child layout"
