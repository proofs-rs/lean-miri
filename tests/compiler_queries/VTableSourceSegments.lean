import Miri.Input.Decoder
import Miri.Input.WorldVTableSegments

open Lean Miri.Input GenericSubstitution TraitSelection
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def readSegment (references : Array TraitRef) (value : Json) : Except String (VTableSegments.Segment TraitRef) := do
  if value == .null then return .metadata
  let #[key,flag] ← value.getArr? | throw "malformed source vtable segment oracle"
  let some reference := references[← key.getNat?]? | throw "source vtable segment oracle key absent"
  pure (.ownEntries reference (← flag.getBool?))

def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath,policy] := args | throw (IO.userError "source oracle no_trait_vptr")
  unless policy == "true" || policy == "false" do throw (IO.userError "explicit no_trait_vptr policy required")
  let noTraitVptr := policy == "true"
  let original := (← must (decodeJson (← IO.FS.readFile sourcePath))).document
  let document := {original with compilerPredicates := #[], queries := {original.queries with vtables := #[]}}
  let context ← must (AliasRuntime.Context.ofDocument document)
  let rows ← must ((← must (Json.parse (← IO.FS.readFile oraclePath))).getArr?)
  unless rows.size == 16 do throw (IO.userError "source vtable arrangement oracle incomplete")
  let references ← must (rows.mapM fun row => do Codec.readTraitRef (← row.getObjVal? "trait_ref"))
  let metadata ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let world ← must ((RuntimeArrayTypes.create metadata).mapError (fun error => reprStr error))
  for index in [:rows.size] do
    let some row := rows[index]? | throw (IO.userError "vtable source row absent")
    let some reference := references[index]? | throw (IO.userError "vtable source reference absent")
    let supers ← must (WorldVTableSegments.directSupertraits context 100000 4096 reference)
    let expectedSupers ← must ((← must ((← must (row.getObjVal? "supers")).getArr?)).mapM fun key => do
      let some reference := references[← key.getNat?]? | throw "vtable source parent key absent"
      pure reference)
    unless supers == expectedSupers do throw (IO.userError "raw supertrait source order differs from pinned compiler")
    let own ← must (WorldDynMethods.ownMethods context 100000 4096 reference.definition)
    let expectedOwn ← must ((← must (row.getObjVal? "own")).getBool?)
    unless !own.isEmpty == expectedOwn do throw (IO.userError "source vtable own-method eligibility differs from compiler")
    let expected ← must ((← must ((← must (row.getObjVal? "segments")).getArr?)).mapM (readSegment references))
    let (actual,_) ← must ((WorldVTableSegments.query 100000 4096 noTraitVptr reference).run world)
    unless actual == expected do throw (IO.userError "source World vtable segments differ from pinned compiler")
  IO.println s!"PASS 16 source World vtable arrangements with no_trait_vptr={noTraitVptr}, raw supertrait order and source method eligibility"
