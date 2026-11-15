import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceSignatureTypes
open Lean Miri Miri.Input Miri.Frontend.Foundation
private def checked (r : Except String α) : IO α := match r with
| .ok a => pure a | .error e => throw (IO.userError e)
private def rejects (r : Except String α) : IO Unit := match r with
| .error _ => pure () | .ok _ => throw (IO.userError "unsupported bound nominal signature accepted")
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "usage: finite std source")
  let document ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
  let initial ← checked (compilerEntrySeed document)
  let some source := initial.canonical.sourceMaterial | throw (IO.userError "source absent")
  let some material := source.physical | throw (IO.userError "source physical expressions absent")
  let mut count := 0
  let mut staticSeen := false
  for (expression,reference) in material.types.zipIdx do
    if let .nominal .. := expression then
      if let .ok concrete := SourceTypes.instantiate material #[] #[] reference then
        if let .ok (world,expected) := SourcePhysical.intern initial concrete then
          let (same,actual) ← checked (SourceSignatureTypes.intern world #[] #[] #[] reference)
          unless actual == expected && same.canonical.types.size == world.canonical.types.size do
            throw (IO.userError "nominal original signature changed canonical identity/layout")
          rejects (SourceSignatureTypes.intern world #[] #[] #[.region .anonymous] reference)
          staticSeen := staticSeen || world.canonical.types.any (fun node => match node.shape with
            | .dynamicTraitObject _ _ .Static => true | _ => false)
          count := count+1
  unless count > 0 do throw (IO.userError "no genuine concrete nominal signature tested")
  unless staticSeen do throw (IO.userError "static existential region control absent")
  IO.println s!"PASS {count} genuine nominal signature identities/full layouts, preserved static regions and HRTB rejection"
