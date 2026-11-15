import Miri.Frontend.FoundationTypeRegistry

open Lean Miri.Frontend.Foundation

private def load (path : String) : IO Document := do
  let text ← IO.FS.readFile path
  match Json.parse text >>= decode with
  | .ok d => pure d
  | .error e => throw (IO.userError e)

private def expect (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error e => throw (IO.userError e)

def main (args : List String) : IO Unit := do
  let u16 : ConcreteType := .primitive "uint" "u16"
  unless sameConcrete 1024 (.array u16 3) (.array u16 3) do
    throw (IO.userError "equal array types differ")
  if sameConcrete 1024 (.array u16 3) (.array u16 4) then
    throw (IO.userError "different array lengths alias")
  match args with
  | [] => IO.println "foundation type registry: structural checks passed"
  | [path] =>
    let d ← load path
    let start := TypeRegistry.start d
    let arguments := #[some u16, none]
    let (first, firstId) ← expect (start.internSource 2 arguments #[none, some 3])
    let (again, againId) ← expect (first.internSource 2 arguments #[none, some 3])
    unless firstId == againId && again.entries.size == 1 do
      throw (IO.userError "same demand was not canonicalized")
    let (second, secondId) ← expect (again.internSource 2 arguments #[none, some 4])
    unless secondId != firstId && second.entries.size == 2 do
      throw (IO.userError "different instantiations collided")
    unless start.entries.isEmpty do
      throw (IO.userError "immutable starting registry changed")
    let (fresh, freshId) ← expect ((TypeRegistry.start d).internSource 2 arguments #[none, some 3])
    unless freshId == 0 && fresh.entries.size == 1 do
      throw (IO.userError "new run retained previous type IDs")
    IO.println "foundation type registry: fresh generic demands passed"
  | _ => throw (IO.userError "usage: FoundationTypeRegistry [ARRAY_JSON]")
