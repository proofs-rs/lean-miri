import Miri.Input.CompilerNamedConstants

/-! Exact libc `eval_path_scalar` constants. The original compiler row carries
the full `libc::<name>` ValueNS path; this adapter requires that identity at
the demand site before decoding the compiler value. -/
namespace Miri.Input.CompilerLibcConstants
open Lean Miri.Memory Miri.Interpreter

private def exactRecord (prepared : CompilerNamedConstants.Prepared) (name : String) :
    Except String Catalog.NamedConstant := do
  let records := prepared.program.input.queries.namedConstants.getD #[]
  let found := records.filter (·.path == #["libc", name])
  unless found.size == 1 do throw s!"missing or duplicate exact libc compiler constant query libc::{name}"
  let some record := found[0]? | throw s!"missing exact libc compiler constant query libc::{name}"
  unless record.name == name do throw "libc compiler constant row name does not match its path"
  pure record

def scalar (prepared : CompilerNamedConstants.Prepared) (name : String) :
    Except String (Scalar P) := do
  let _ ← exactRecord prepared name
  CompilerNamedConstants.scalar prepared name

/-- Integer helpers preserve the canonical named-constant conversion after
checking the exact source path, for source wrappers using `eval_libc_i32`. -/
def i32 (prepared : CompilerNamedConstants.Prepared) (name : String) :
    Except String Int32 := do
  let _ ← exactRecord prepared name
  CompilerNamedConstants.i32 prepared name

end Miri.Input.CompilerLibcConstants
