import Miri.Frontend.FoundationSourceMaterial
import Miri.Input.SourceTraitSelection
open Lean Miri Miri.Input Miri.Frontend.Foundation

private def reject (label : String) (value : Except String Bool) : IO Unit :=
  match value with
  | .ok _ => throw (IO.userError s!"accepted {label}")
  | .error _ => pure ()

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected genuine std finite trait source")
  let document ← IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= decode)
  let source ← IO.ofExcept (typedSourceMaterial document)
  let some physical := source.physical | throw (IO.userError "source types absent")
  let some abi := source.abi | throw (IO.userError "source ABI absent")
  let some traits := source.traitImpls | throw (IO.userError "source trait declarations absent")
  let [definition] := (physical.definitions.filter (·.path == "std::panic::UnwindSafe")).toList
    | throw (IO.userError "genuine UnwindSafe declaration absent")
  let [closure] := (physical.types.filterMap fun type => match type with
    | .closure closure =>
      if physical.definitions[closure.definition]?.map (·.path) == some "std::rt::lang_start_internal::{closure#0}" then some closure else none
    | _ => none).toList | throw (IO.userError "genuine internal closure absent")
  let some closureId := physical.types.findIdx? (· == .closure closure)
    | throw (IO.userError "closure source reference absent")
  let type ← IO.ofExcept (SourceTypes.instantiate physical #[] #[] closureId)
  let check := SourceTraitSelection.check physical abi traits
    (fun _ _ => throw "unexpected builtin condition in this genuine source") definition.raw
  unless (← IO.ofExcept (check type)) do throw (IO.userError "genuine closure UnwindSafe proof failed")
  let byte := SourceTypes.Concrete.primitive "uint" "u8"
  unless (← IO.ofExcept (check (.pointer "raw_pointer_const" byte))) do
    throw (IO.userError "raw-pointer conditional impl failed")
  unless (← IO.ofExcept (check (.pointer "reference_erased_const" byte))) do
    throw (IO.userError "shared-reference conditional impl failed")
  match check (.pointer "reference_erased_mut" byte) with
  | .ok false => pure ()
  | _ => throw (IO.userError "mutable-reference negative impl was not proved false")
  let incomplete := {traits with declarations := traits.declarations.filter (·.definition != definition.raw)}
  reject "missing complete trait declaration" (SourceTraitSelection.check physical abi incomplete
    (fun _ _ => throw "unexpected builtin") definition.raw type)
  let ambiguous := {traits with declarations := traits.declarations ++ traits.declarations.filter (·.definition == definition.raw)}
  reject "ambiguous trait declaration" (SourceTraitSelection.check physical abi ambiguous
    (fun _ _ => throw "unexpected builtin") definition.raw type)
  IO.println "genuine closure/manual conditional auto-trait proof and negative controls passed"
