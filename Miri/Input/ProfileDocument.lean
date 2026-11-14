import Miri.Input.Decoder

/-! Profile selection precedes legacy decoding. The initial descriptor remains
raw until preparation interns all symbols in its execution-owned type World. -/
namespace Miri.Input.ProfileDocument
open Lean
set_option autoImplicit false

structure Initial where
  input : ExecutionInput
  originalDocument : String
  snapshot : Json
  ctfeRoots : Array Json
  selectedCache : Array Json

inductive Decoded where
  | legacy (input : ExecutionInput)
  | initial (input : Initial)

def Decoded.input : Decoded → ExecutionInput
  | .legacy input => input
  | .initial source => source.input

private structure Presence where
  snapshot : Bool := false
  roots : Bool := false
  selected : Bool := false
private def profileFields (text : String) : Except String Presence :=
  JsonReader.run (JsonReader.object ({} : Presence) fun found key => do
    JsonReader.skipValue
    pure {snapshot := found.snapshot || key == "compiler_initial_global_snapshot"
          roots := found.roots || key == "compiler_initial_ctfe_roots"
          selected := found.selected || key == "compiler_initial_selected_query_cache"}) text

def decodeProfiled (text : String) (profile : Options) : Except String Decoded := do
  let present ← profileFields text
  unless present.snapshot || present.roots || present.selected do
    return .legacy (← Miri.Input.decodeJsonProfiled text profile)
  unless present.snapshot do
    throw "initial compiler query/body profiles require an explicit complete initial allocation snapshot"
  let (input,snapshot,roots,selected) ← Miri.Input.decodeInitialQueryProfiled text profile
  return .initial ⟨input,text,snapshot,roots,selected.getD #[]⟩

end Miri.Input.ProfileDocument
