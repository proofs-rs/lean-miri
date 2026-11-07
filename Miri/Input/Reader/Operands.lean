import Miri.Input.Reader.Places
import Miri.Input.Reader.Constants

namespace Miri.Input.Reader.OperandReader
open Lean Miri.MIR

abbrev State := MIRReader.State
abbrev Decode := MIRReader.Decode

def place := PlaceReader.place

private def constant (catalog : Catalog) (ctx : ConstantReader.Context) (input : Json) (path : String) : Decode ConstantId := do
  return ⟨← ConstantReader.constant catalog ctx input path⟩

private def value (catalog : Catalog) (ctx : ConstantReader.Context) (input : Json) (path : String) : Decode OperandNode := do
  catalog.requireSupported input path
  let field := fun key => catalog.field input key path
  match ← catalog.string (← field "kind") path with
  | "Copy" => return .Copy (← place catalog ctx.typeCount (← field "place") path)
  | "Move" => return .Move (← place catalog ctx.typeCount (← field "place") path)
  | "Constant" => return .Constant (← constant catalog ctx (← field "constant") path)
  | "RuntimeChecks" =>
    match ← catalog.string (← catalog.field (← field "check") "kind" path) path with
    | "ub_checks" => return .RuntimeChecks .UbChecks
    | "contract_checks" => return .RuntimeChecks .ContractChecks
    | "overflow_checks" => return .RuntimeChecks .OverflowChecks
    | kind => throw s!"{path}: unsupported runtime check {kind}"
  | kind => throw s!"{path}: unsupported operand {kind}"

def operand (catalog : Catalog) (ctx : ConstantReader.Context) (input : Json) (path : String) : Decode OperandId := do
  return ⟨← catalog.readCached (·.tables.operands) (fun state operands => {state with tables := {state.tables with operands}})
    (value catalog ctx) input path⟩

def operands (catalog : Catalog) (ctx : ConstantReader.Context) (input : Json) (path : String) : Decode OperandListId := do
  return ⟨← catalog.readCached (·.tables.operandLists) (fun state operandLists => {state with tables := {state.tables with operandLists}})
    (fun input path => do
      (← catalog.array input path).mapIdxM fun index input =>
        operand catalog ctx input s!"{path}[{index}]") input path⟩

end Miri.Input.Reader.OperandReader
