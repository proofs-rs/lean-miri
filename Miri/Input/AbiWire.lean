import Lean

/-! Positional ABI transport, version 1. These records are data, not evidence
of a supported ABI. The ordinary layout/mode/ABI validators still own that check.
Canonical JSON views preserve all existing consumers and diagnostic traversal. -/
namespace Miri.Input.AbiWire
open Lean

def argumentMarker : String := "$lean_miri_abi_arg"
def functionMarker : String := "$lean_miri_fn_abi"

structure Argument where
  typeId : Nat
  layout : Json
  mode : Json

structure Function where
  argumentVector : Option Nat
  returnId : Nat
  convention : Json
  canUnwind : Bool
  cVariadic : Bool
  fixedCount : Nat

inductive Record where
  | argument (value : Argument)
  | function (value : Function)

structure Table where
  arguments : Std.HashMap Nat Argument := {}
  vectors : Std.HashMap Nat (Array Nat) := {}
  functions : Array Function := #[]

def Argument.toJson (value : Argument) : Json := Json.mkObj [
  ("type", Json.mkObj [("type_id", Lean.toJson value.typeId)]),
  ("layout", value.layout), ("mode", value.mode)]

def Function.toJson (value : Function) (arguments returned : Json) : Json := Json.mkObj [
  ("arguments", arguments), ("return", returned), ("calling_convention", value.convention),
  ("can_unwind", Lean.toJson value.canUnwind), ("c_variadic", Lean.toJson value.cVariadic),
  ("fixed_count", Lean.toJson value.fixedCount)]

private def reference (id : Nat) : Json :=
  Json.mkObj [("$lean_miri_shared_ref", Lean.toJson id)]

/-- Reconstruct only the raw header; its edges still refer to earlier nodes.
This lets the existing traversal builder retain all original DAG identities. -/
def Record.toRawJson : Record → Json
  | .argument value => value.toJson
  | .function value => value.toJson
      (value.argumentVector.map reference |>.getD (.arr #[])) (reference value.returnId)

def hasMarker (value : Json) : Bool :=
  match value with
  | .obj fields => fields.contains argumentMarker || fields.contains functionMarker
  | _ => false

private def slot (values : Array Json) (index : Nat) (path : String) : Except String Json :=
  match values[index]? with
  | some value => pure value
  | none => throw s!"{path}: missing slot {index}"

private def natural (value : Json) (path : String) : Except String Nat :=
  value.getNat? |>.mapError fun _ => s!"{path}: expected unsigned integer"

private def boolean (value : Json) (path : String) : Except String Bool :=
  value.getBool? |>.mapError fun _ => s!"{path}: expected boolean"

def parse (value : Json) (path : String) : Except String (Option Record) := do
  if !hasMarker value then return none
  let .obj fields := value | throw s!"{path}: typed ABI record must be an object"
  unless fields.toList.length == 1 do throw s!"{path}: typed ABI record has extra fields"
  if let .ok raw := value.getObjVal? argumentMarker then
    let values ← raw.getArr? |>.mapError fun _ => s!"{path}: ABI argument requires an array"
    unless values.size == 3 do throw s!"{path}: ABI argument requires exactly 3 slots"
    return some (.argument ⟨← natural (← slot values 0 path) s!"{path}[0]",
      ← slot values 1 path, ← slot values 2 path⟩)
  let raw ← value.getObjVal? functionMarker
  let values ← raw.getArr? |>.mapError fun _ => s!"{path}: function ABI requires an array"
  unless values.size == 6 do throw s!"{path}: function ABI requires exactly 6 slots"
  let arguments ← match ← slot values 0 path with
    | .null => pure none
    | other => some <$> natural other s!"{path}[0]"
  return some (.function ⟨arguments, ← natural (← slot values 1 path) s!"{path}[1]",
    ← slot values 2 path, ← boolean (← slot values 3 path) s!"{path}[3]",
    ← boolean (← slot values 4 path) s!"{path}[4]",
    ← natural (← slot values 5 path) s!"{path}[5]"⟩)

private def referenceId? (value : Json) : Option Nat := do
  let .obj fields := value | none
  let raw ← fields["$lean_miri_shared_ref"]?
  if fields.toList.length != 1 then none else raw.getNat?.toOption

/-- Ordinary shared arrays keep their IDs. Record only arrays of already checked
ABI argument transport nodes; a function cannot reinterpret arbitrary data as one. -/
def argumentVector? (table : Table) (value : Json) : Option (Array Nat) := do
  match value with
  | .arr values =>
    values.mapM fun child => do
      let id ← referenceId? child
      if table.arguments.contains id then some id else none
  | _ => table.vectors[← referenceId? value]?

end Miri.Input.AbiWire
