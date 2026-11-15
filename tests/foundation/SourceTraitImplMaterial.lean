import Miri.Frontend.FoundationSourceMaterial
open Lean Miri Miri.Input Miri.Frontend.Foundation
private def checked (r : Except String α) : IO α := match r with
| .ok value => pure value | .error e => throw (IO.userError e)
private def rejects (r : Except String α) : IO Unit := match r with
| .error _ => pure () | .ok _ => throw (IO.userError "malformed trait impl source accepted")
private def replace (j : Json) (key : String) (value : Json) : Except String Json := do
  return Json.mkObj (((← j.getObj?).toArray.toList.filter (·.1 != key)) ++ [(key,value)])
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected genuine generic auto source")
  let d ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
  let material ← checked (typedSourceMaterial d)
  let some source := material.traitImpls | throw (IO.userError "trait impl source absent")
  let some physical := material.physical | throw (IO.userError "physical source absent")
  let mut detailed := 0
  let mut rigidCount := 0
  for declaration in source.declarations do
    unless declaration.isAuto do throw (IO.userError "observed generic auto identity lost")
    for implementation in declaration.implementations do
      if let some header := implementation.header then
        detailed := detailed+1
        unless header.traitArguments[0]? == some header.selfType do throw (IO.userError "Self identity lost")
      else rigidCount := rigidCount+1
  unless source.declarations.size >= 2 && detailed > 0 && rigidCount > 0 do throw (IO.userError "genuine complete headers/details absent")
  let raw ← checked (d.source.getObjVal? "trait_impl_source")
  let rows ← checked (raw.getObjValAs? (Array Json) "declarations")
  let some first := rows[0]? | throw (IO.userError "declaration absent")
  let items ← checked (first.getObjValAs? (Array Json) "implementations")
  let some item := items[0]? | throw (IO.userError "impl absent")
  let badItem ← checked (replace item "polarity" (toJson "Unknown"))
  let badFirst ← checked (replace first "implementations" (toJson (#[badItem] ++ items.drop 1)))
  let badRaw ← checked (replace raw "declarations" (toJson (#[badFirst] ++ rows.drop 1)))
  let badSource ← checked (replace d.source "trait_impl_source" badRaw)
  rejects (SourceTraitImplsParser.material {d with source := badSource} physical)
  let duplicate ← checked (replace raw "declarations" (toJson (rows.push first)))
  rejects (SourceTraitImplsParser.material {d with source := ← checked (replace d.source "trait_impl_source" duplicate)} physical)
  let mut detailedControls := 0
  for row in rows do
    for item in (← checked (row.getObjValAs? (Array Json) "implementations")) do
      let sourceHeader ← checked (item.getObjVal? "syntax")
      if sourceHeader != .null then
        for (field,value) in #[("constness",toJson "Unknown"),("self_type",toJson physical.types.size)] do
          let badHeader ← checked (replace sourceHeader field value)
          let badItem ← checked (replace item "syntax" badHeader)
          let badRow ← checked (replace row "implementations" (toJson #[badItem]))
          let badRaw ← checked (replace raw "declarations" (toJson #[badRow]))
          rejects (SourceTraitImplsParser.material {d with source := ← checked (replace d.source "trait_impl_source" badRaw)} physical)
        detailedControls := detailedControls+1
  unless detailedControls > 0 do throw (IO.userError "conditional header controls absent")
  IO.println s!"PASS {source.declarations.size} reachable auto declarations, {detailed} full generic headers/{rigidCount} rigid-only headers; invalid polarity/duplicate reject"
