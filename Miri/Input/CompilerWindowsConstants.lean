import Miri.Input.CompilerNamedConstants

/-! Exact `helpers.rs::eval_windows` ValueNS constants. The compiler query
identity is `std::sys::pal::windows::<module>::<name>`; the adapter validates
the complete path before reusing the canonical named-constant decoder. -/
namespace Miri.Input.CompilerWindowsConstants
open Lean Miri.Memory Miri.Interpreter

def scalar (prepared : CompilerNamedConstants.Prepared) (module name : String) :
    Except String (Scalar Provenance) := do
  let records := prepared.program.input.queries.namedConstants.getD #[]
  let found := records.filter (·.path == #["std", "sys", "pal", "windows", module, name])
  unless found.size == 1 do
    throw s!"missing or duplicate exact Windows compiler constant query std::sys::pal::windows::{module}::{name}"
  let some record := found[0]? | throw "Windows compiler constant query absent"
  unless record.name == name do throw "Windows compiler constant row name does not match its path"
  CompilerNamedConstants.scalar prepared name
end Miri.Input.CompilerWindowsConstants
