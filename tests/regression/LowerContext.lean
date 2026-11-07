import Miri.Input.LowerMIR

open Miri.Input

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let context : LowerContext := {
    typeIds := #[0, 1, 2]
    scalarSizes := #[some 8, none, some 4]
    allocationIds := #[0, 1] }
  check (context.containsTypeId 2 && !context.containsTypeId 3) "type bound incorrect"
  check (context.containsAllocationId 1 && !context.containsAllocationId 2) "allocation bound incorrect"
  check (context.scalarSize 0 == some 8 && context.scalarSize 1 == none && context.scalarSize 4 == none)
    "missing scalar width acquired a value"
  let malformed := {context with typeIds := #[1, 0, 2], allocationIds := #[1, 0]}
  check (!malformed.containsTypeId 0 && !malformed.containsAllocationId 0)
    "misindexed identity accepted"
  if let some path := args.head? then
    let .ok decoded := decodeJson (← IO.FS.readFile path)
      | throw (IO.userError "input decode failed")
    let some body := decoded.document.bodies[0]? | throw (IO.userError "root body missing")
    let context := LowerContext.ofDocument decoded.document
    check ((lowerBody context body.toBodyCore).isOk) "root body did not lower"
    let .error _ := lowerBody {context with typeIds := #[]} body.toBodyCore
      | throw (IO.userError "body with missing source types lowered")
  IO.println "lowering table bounds: PASS"
