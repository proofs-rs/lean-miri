import Miri.Input.LowerMIR
import Miri.Input.Decoder

open Miri.Input

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let context : LowerContext := {typeIds := #[1,3,3], allocationIds := #[7,7]}
  check (context.containsTypeId 1 && context.containsTypeId 3 && !context.containsTypeId 7)
    "type IDs crossed the allocation namespace"
  check (context.containsAllocationId 7 && !context.containsAllocationId 1)
    "allocation IDs crossed the type namespace"
  let changed := (context.withTypeIds #[9,9]).withAllocationIds #[2,2]
  check (changed.containsTypeId 9 && !changed.containsTypeId 1 &&
    changed.containsAllocationId 2 && !changed.containsAllocationId 7)
    "context retained obsolete pool IDs"
  if let some path := args.head? then
    let .ok decoded := decodeJson (← IO.FS.readFile path)
      | throw (IO.userError "input decode failed")
    let some body := decoded.document.bodies[0]?
      | throw (IO.userError "input has no body")
    let context := LowerContext.ofDocument decoded.document
    let .ok prepared := lowerBody context body.toBodyCore
      | throw (IO.userError "body preparation failed")
    check (prepared.body == body.mir) "preparation changed decoded MIR"
    check (prepared.definitions == decoded.document.definitions)
      "preparation changed definition identities"
    check (prepared.spans == decoded.document.spans && prepared.typeConstants == decoded.document.typeConstants)
      "preparation changed compiler pools"
    for ty in decoded.document.types do
      check (context.containsTypeId ty.id) "prepared context omitted compiler type"
    for allocation in decoded.document.allocations do
      check (context.containsAllocationId allocation.id) "prepared context omitted compiler allocation"
  IO.println "preparation preserves compiler pool identities and namespaces"
