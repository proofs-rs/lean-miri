import MiriTests.Input.LegacyFixture
import Miri.Input.LowerMIR
import Miri.Input.Decoder
import Miri.Input.CompilerInstance

open Miri.Input

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def instanceRow (kind : Miri.Interpreter.CallInstanceKind)
    (args : Array Miri.MIR.GenericArg := #[]) : InstanceNode := {
  instanceKind := kind, genericArgs := args, id := 0, kind := .identityOnly,
  defPath := none, definitionId := none, bodyId := none, promotedBodies := #[] }

private def checkInstances : IO Unit := do
  let rows := #[instanceRow (.Item 7) #[.Type 3], instanceRow (.Item 7) #[.Type 4],
    instanceRow (.Virtual 8 0), instanceRow (.Shim (.DropGlue 9 none))]
  check (CompilerInstance.item rows 7 #[.Type 3] == .ok 0 &&
    CompilerInstance.item rows 7 #[.Type 4] == .ok 1)
    "instance lookup merged distinct generic arguments"
  check (CompilerInstance.definitionOf rows 2 == .ok 8 &&
    CompilerInstance.definitionOf rows 3 == .ok 9)
    "instance lookup discarded a virtual or shim definition"
  for definition in #[8,9,10] do
    check (CompilerInstance.item rows definition #[] ==
      .error "exact compiler Item instance is absent")
      "item lookup accepted a non-Item or absent definition"
  check (CompilerInstance.item (rows.push (instanceRow (.Item 7) #[.Type 3])) 7 #[.Type 3] ==
    .error "duplicate canonical Item instance identity")
    "item lookup accepted duplicate exact identities"
  let expected := "compiler instance ID 4 out of bounds"
  check (match CompilerInstance.source rows 4 with
    | .error message => message == expected | .ok _ => false)
    "instance source did not reject an out-of-bounds ID"
  check (CompilerInstance.kindOf rows 4 == .error expected &&
    CompilerInstance.argsOf rows 4 == .error expected &&
    CompilerInstance.definitionOf rows 4 == .error expected)
    "instance projections changed the bounds error"

def main (args : List String) : IO Unit := do
  checkInstances
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
    let .ok decoded := decodeFixture (← IO.FS.readFile path)
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
