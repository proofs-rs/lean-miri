import Miri.Input.CompilerNamedConstants

/-! Exact `helpers.rs::eval_windows` ValueNS constants. The compiler query
identity is `std::sys::pal::windows::<module>::<name>`; the adapter validates
the complete path before reusing the canonical named-constant decoder. -/
namespace Miri.Input.CompilerWindowsConstants
open Lean Miri.Memory Miri.Interpreter

/-- Resolve the exact source path and retain canonical scalar validation. -/
def scalar (prepared : CompilerNamedConstants.Prepared) (module name : String) :
    Except String (Scalar Provenance) := do
  let mut found := 0
  for entry in prepared.entries do
    if entry.path.toOption == some #["std","sys","pal","windows",module,name] then
      unless entry.name == name do throw "Windows compiler constant row name does not match its path"
      found := found + 1
  unless found == 1 do
    throw s!"missing or duplicate exact Windows compiler constant query std::sys::pal::windows::{module}::{name}"
  CompilerNamedConstants.scalar prepared name

end Miri.Input.CompilerWindowsConstants
