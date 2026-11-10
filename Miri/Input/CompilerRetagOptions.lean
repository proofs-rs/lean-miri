import Miri.Input.CompilerProviders
import Miri.Input.EvalRetagMachine

/-! Tree Borrows machine parameters and the exact protected-frame attribute
query from tree_borrows/mod.rs:143–148,329. Missing evidence fails on demand.
The omitted CreatedPointerTag emission is diagnostics.rs::emit_diagnostic,
which returns unit and changes no interpreter state. Tag allocation and
protector registration remain in the actual retag implementation. -/
namespace Miri.Input.CompilerRetagOptions
open Lean Miri.MIR Miri.Interpreter

/-- These are the two actual TreeBorrowsParams, fixed for an execution. -/
structure Options where
  implicitWrites : Bool
  preciseInteriorMut : Bool

def rustcNoWritable (p : CompilerProviders.Prepared) (id : DefId) : Except String Bool := do
  let some _ := p.program.compilerTables.definitions[id]?
    | throw "retag frame absent from canonical compiler definition table"
  let mut selected : Option Bool := none
  let mut seen : Array Nat := #[]
  for row in p.program.input.queries.retag do
    let key := row.definition
    unless key < p.program.compilerTables.definitions.size do throw "retag compiler definition ID out of bounds"
    if seen.contains key then throw "duplicate compiler retag definition query"
    seen := seen.push key
    if key == id then selected := some row.rustcNoWritable
  let some value := selected | throw "exact compiler retag frame attribute query absent"
  pure value

def make (p : CompilerProviders.Prepared) (options : Options) : EvalRetagMachine.Leaves K U where
  implicitWrites := pure options.implicitWrites
  preciseInteriorMut := pure options.preciseInteriorMut
  rustcNoWritable := fun id =>
    match rustcNoWritable p id with
    | .ok value => pure value
    | .error reason => throw (.unsupported reason)
  logCreation := fun _ _ _ _ _ => pure ()
end Miri.Input.CompilerRetagOptions
