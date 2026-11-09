import Lean

/-! Cast query records carry their results directly alongside their exact keys.
The resolution-kind tag preserves a genuine optional function-pointer target;
an absent target carries no instance reference. -/
namespace Miri.Input.CompilerCastQueryRecord
open Lean

def payload (record : Json) : Except String Json := do
  unless (← (← record.getObjVal? "typing_env").getStr?) == "fully_monomorphized" do
    throw "cast query typing environment mismatch"
  pure record

def functionResult (record : Json) : Except String (Option Json) := do
  let record ← payload record
  if let some kind := (record.getObjVal? "resolution_kind").toOption then
    match ← kind.getStr? with
    | "none" =>
      if (record.getObjVal? "instance_id").isOk then
        throw "absent cast resolution carries an instance identity"
      return none
    | "instance" => pure ()
    | _ => throw "unrecognized cast resolution kind"
  -- An instance ID determines a positive answer; the tag distinguishes an
  -- absent result that has no instance identity.
  let _ ← (← record.getObjVal? "instance_id").getNat?
  return some record

end Miri.Input.CompilerCastQueryRecord
