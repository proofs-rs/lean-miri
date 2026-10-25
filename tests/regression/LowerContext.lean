import Miri.Input.LowerMIR
import Miri.Input.Decoder

open Miri.Input

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let manual : LowerContext := {
    typeIds := #[1, 3, 3]
    scalarSizes := #[(1, 8), (1, 16), (3, 4)]
    allocationIds := #[7, 7] }
  let indexed := ((manual.withTypeIds manual.typeIds).withAllocationIds manual.allocationIds)
    |>.withScalarSizes manual.scalarSizes
  for id in #[0, 1, 3, 7, 9] do
    check (manual.containsTypeId id == indexed.containsTypeId id)
      s!"type membership changed at {id}"
    check (manual.containsAllocationId id == indexed.containsAllocationId id)
      s!"allocation membership changed at {id}"
    check (manual.scalarSize id == indexed.scalarSize id)
      s!"scalar width changed at {id}"
  check (indexed.scalarSize 1 == some 8) "first duplicate scalar width was not retained"
  let rebased := ((indexed.withTypeIds #[9, 9]).withAllocationIds #[2, 2])
    |>.withScalarSizes #[(3, 64), (3, 128), (9, 2)]
  let equivalent : LowerContext := {
    typeIds := #[9, 9]
    scalarSizes := #[(3, 64), (3, 128), (9, 2)]
    allocationIds := #[2, 2] }
  for id in #[0, 1, 2, 3, 7, 9] do
    check (rebased.containsTypeId id == equivalent.containsTypeId id)
      s!"rebased type membership mismatch at {id}"
    check (rebased.containsAllocationId id == equivalent.containsAllocationId id)
      s!"rebased allocation membership mismatch at {id}"
    check (rebased.scalarSize id == equivalent.scalarSize id)
      s!"rebased scalar width mismatch at {id}"
  check (rebased.scalarSize 3 == some 64 && rebased.scalarSize 1 == none)
    "rebased scalar first-match or obsolete entry mismatch"
  if let some path := args.head? then
    let .ok decoded := decodeJson (← IO.FS.readFile path)
      | throw (IO.userError "genuine input decode failed")
    let some body := decoded.document.bodies[0]?
      | throw (IO.userError "genuine input has no root body")
    let core := body.toBodyCore
    let indexedCtx := LowerContext.ofDocument decoded.document
    let manualCtx : LowerContext := { indexedCtx with
      typeIndex := none, allocationIndex := none, scalarIndex := none }
    check ((lowerBody indexedCtx core).isOk && (lowerBody manualCtx core).isOk)
      "genuine baseline body did not lower under both paths"
    let noTypesIndexed := indexedCtx.withTypeIds #[]
    let noTypesManual : LowerContext := {
      typeIds := #[], scalarSizes := manualCtx.scalarSizes
      allocationIds := manualCtx.allocationIds, obligations := manualCtx.obligations
      sourceDocument := manualCtx.sourceDocument }
    let .error indexedError := lowerBody noTypesIndexed core
      | throw (IO.userError "indexed missing-type case unexpectedly lowered")
    let .error manualError := lowerBody noTypesManual core
      | throw (IO.userError "manual missing-type case unexpectedly lowered")
    check (indexedError == manualError) "missing-type error order changed"
    let noSizesIndexed := indexedCtx.withScalarSizes #[]
    let noSizesManual : LowerContext := {
      typeIds := manualCtx.typeIds, scalarSizes := #[]
      allocationIds := manualCtx.allocationIds, obligations := manualCtx.obligations
      sourceDocument := manualCtx.sourceDocument }
    match lowerBody noSizesIndexed core, lowerBody noSizesManual core with
    | .error indexedError, .error manualError =>
      check (indexedError == manualError) "missing-scalar error order changed"
    | .ok _, .ok _ => pure ()
    | _, _ => throw (IO.userError "missing-scalar success/error outcome changed")
    IO.println "source146 genuine manual/indexed body/error equivalence PASS"
  IO.println "source146 LowerContext manual/indexed/rebased equivalence PASS"
