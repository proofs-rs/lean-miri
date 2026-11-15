import Miri.Frontend.FoundationTarget

open Lean Miri.Frontend.Foundation

private def replace (j : Json) (key : String) (value : Json) : Except String Json := do
  let obj ← j.getObj?
  return .mkObj ((obj.toArray.toList.filter fun entry => entry.1 != key) ++ [(key, value)])

private def mutate (j : Json) (key : String) (value : Json) : Except String Json := do
  let target ← j.getObjVal? "target"
  let evidence ← target.getObjVal? "runtime_data_layout"
  replace j "target" (← replace target "runtime_data_layout" (← replace evidence key value))

private def rejects (j : Json) : IO Unit := do
  match runtimeTarget j with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid target accepted")

def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "usage: FoundationTarget.lean FOUNDATION_JSON")
  let source ← IO.FS.readFile path
  let json ← IO.ofExcept (Json.parse source)
  let evidence ← IO.ofExcept (targetEvidence json)
  let _ ← IO.ofExcept (runtimeTarget json)
  unless evidence.pointerWidthBits == 64 && evidence.i8AlignBytes == 1 do
    throw (IO.userError "expected pinned x86_64 fixture target")
  for (key, value) in [
      ("i32_align_bytes", toJson (3 : Nat)),
      ("pointer_width_bits", toJson (32 : Nat)),
      ("object_size_bound_bytes", toJson (1 : Nat)),
      ("c_enum_min_size", toJson "unknown"),
      ("instruction_address_space", toJson (4294967296 : Nat))] do
    rejects (← IO.ofExcept (mutate json key value))
  let target ← IO.ofExcept (json.getObjVal? "target")
  let material ← IO.ofExcept (target.getObjVal? "runtime_data_layout")
  let spec ← IO.ofExcept (material.getObjVal? "default_address_space_pointer_spec")
  let badSpace := Json.mkObj [
    ("address_space", toJson (42 : Nat)), ("spec", spec),
    ("object_size_bound_bytes", toJson (1 : Nat))]
  rejects (← IO.ofExcept (mutate json "address_space_info" (.arr #[badSpace])))
  rejects (← IO.ofExcept (replace json "target" (← IO.ofExcept (replace target "runtime_data_layout" Json.null))))
  IO.println "foundation target: genuine target import and 7 rejection checks passed"
