import Miri.Frontend.Foundation

/-! Finite source entry selection. Process startup additionally needs generic
instance resolution, function-pointer physical types, lang_start MIR/ABI and a
compiler allocation-identity world; this module supplies none of those facts. -/
namespace Miri.Frontend.Foundation
open Lean

structure SelectedCompilerEntry where
  definition : Nat
  sigpipe : UInt8
  deriving Repr, DecidableEq

structure EntrySelection where
  compilerEntry : Option SelectedCompilerEntry
  startLangItem : Option Nat
  deriving Repr, DecidableEq

/-- Read exact rustc entry_fn and start language-item selection, preserving an
absent entry for library roots such as generic identity. -/
def entrySelection (document : Json) : Except String EntrySelection := do
  let definitions ← document.getObjValAs? (Array Json) "definitions"
  let material ← document.getObjVal? "entry_selection"
  let start ← material.getObjValAs? (Option Nat) "start_lang_item"
  if let some id := start then
    unless id < definitions.size do throw "start language-item definition out of bounds"
  let entry ← material.getObjValAs? (Option Json) "compiler_entry"
  let entry ← entry.mapM fun value => do
    let definition ← value.getObjValAs? Nat "definition"
    unless definition < definitions.size do throw "compiler entry definition out of bounds"
    unless (← value.getObjValAs? String "kind") == "rustc_main" do
      throw "unsupported compiler entry kind"
    let sigpipe ← value.getObjValAs? Nat "sigpipe"
    unless sigpipe < 256 do throw "compiler entry sigpipe exceeds u8"
    return (⟨definition, UInt8.ofNat sigpipe⟩ : SelectedCompilerEntry)
  return ⟨entry, start⟩

end Miri.Frontend.Foundation
