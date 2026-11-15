import Miri.Frontend.FoundationSourceMaterial
import Miri.Input.Decoder
import Miri.Input.SourceSignatureTypes
import Miri.Input.SourceMirReferences
open Lean Miri Miri.Input Miri.Frontend.Foundation
private def rejects (result : Except String A) : IO Unit :=
  match result with | .error _ => pure () | .ok _ => throw (IO.userError "unsupported bound signature accepted")
def main (args : List String) : IO Unit := do
  let [sourcePath,compilerPath] := args | throw (IO.userError "expected source and compiler signature oracle")
  let document ← IO.ofExcept (Json.parse (← IO.FS.readFile sourcePath) >>= decode)
  let material ← IO.ofExcept (typedSourceMaterial document)
  let oracle := (← IO.ofExcept (decodeJson (← IO.FS.readFile compilerPath))).document
  let world ← IO.ofExcept (SourceCompilerWorld.create {oracle with sourceMaterial := some material})
  let some physical := material.physical | throw (IO.userError "typed source types absent")
  let before := world.canonical.types.size
  let mut world := world
  let some abi := material.abi | throw (IO.userError "typed signatures absent")
  let some mir := material.genericMir | throw (IO.userError "typed source MIR absent")
  let roots := (abi.functions.map (·.signature.inputs)).flatten ++ (mir.bodies.map fun body => body.locals.map (·.type)).flatten
  let mut seen : Array Nat := #[]
  let mut checked := 0
  for ref in roots do
    unless !seen.contains ref do continue
    seen := seen.push ref
    let some (.functionPointer signature) := physical.types[ref]? | continue
    unless !signature.boundVariables.isEmpty do continue
    rejects (SourceTypes.instantiate physical #[] #[] ref)
    let (updated,id) ← IO.ofExcept (SourceSignatureTypes.intern world #[] #[] #[] ref)
    unless id < before do throw (IO.userError "original bound FnPtr differs from independent compiler type identity")
    let some row := updated.canonical.types[id]? | throw (IO.userError "canonical FnPtr absent")
    let .functionPointer actual variables := row.shape | throw (IO.userError "bound FnPtr lost shape")
    let (_,expected) ← IO.ofExcept (SourceSignatureTypes.boundVariables updated signature.boundVariables)
    unless variables == expected && actual.safety == signature.safety && actual.abi == signature.abi &&
        actual.cVariadic == signature.cVariadic do throw (IO.userError "binder/signature identity changed")
    let (same,repeated) ← IO.ofExcept (SourceSignatureTypes.intern updated #[] #[] #[] ref)
    unless repeated == id && same.canonical.types.size == updated.canonical.types.size do
      throw (IO.userError "bound signature interning not idempotent")
    let broken := {signature with boundVariables := #[]}
    let physical := {physical with types := physical.types.mapIdx (fun i value => if i == ref then .functionPointer broken else value)}
    let broken := {material with physical := some physical}
    rejects (SourceSignatureTypes.intern {updated with canonical := {updated.canonical with sourceMaterial := some broken}} #[] #[] #[] ref)
    world := updated
    checked := checked+1
  unless checked ≥ 4 do throw (IO.userError "named/anonymous nested binder cases absent")
  for body in mir.bodies do
    let _ ← IO.ofExcept (SourceMirReferences.prepare world body #[] #[])
  IO.println s!"{checked} original bound FnPtr identities/layouts equal compiler; malformed binders reject"
