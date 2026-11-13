import Miri.Input.Decoder
import Miri.Input.CompilerProviders
import Miri.Input.CompilerWorldCompatibility

open Lean Miri.Input Miri.Interpreter TypeArena
private def must [ToString ε] (value : Except ε A) : IO A :=
  match value with | .ok result => pure result | .error error => throw (IO.userError (toString error))
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
private def access : RuntimeArrayQueries.Access RuntimeArrayTypes.World := ⟨id,fun _ next => next⟩
private def run (world : RuntimeArrayTypes.World) (action : EStateM StepError RuntimeArrayTypes.World A) :
    IO (A × RuntimeArrayTypes.World) :=
  match action world with
  | .ok value next => pure (value,next)
  | .error error _ => throw (IO.userError (reprStr error))

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected freshly exported current-schema source")
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let prepared ← must (CompilerProviders.prepare (← must (lowerProgram document)))
  let runtime ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let initial ← must ((RuntimeArrayTypes.create runtime).mapError reprStr)
  let empty ← must (World.ofMaterial #[] #[] document.definitions #[] initial.arena.pointerBytes)
  let mut state := {initial with arena := empty}
  let queries := CompilerWorldCompatibility.queries prepared.lifecycle.calls.symbols.facts.context access
  let mut count := 0
  let mut nonnull := 0
  for node in document.types do
    if let .adt source := node.shape then
      let term ← must (GenericInstantiationWorld.ofType initial.arena 16384 node.id)
      let (fresh,next) ← must ((RuntimeArrayTypes.liftType (GenericInstantiationWorld.resolveType 16384 term)).run state)
      state := next
      let (actual,next) ← run state (queries.adt fresh)
      state := next
      check (actual.variants.size == source.variants.size) "raw ADT variant domain differs"
      for (a,b) in actual.variants.zip source.variants do
        check (a.size == b.fields.size) "raw ADT field domain differs"
        for (field,expected) in a.zip b.fields do
          check (field.name == expected.name) "raw field symbol differs"
          check ((← must (GenericInstantiationWorld.ofType state.arena 16384 field.ty)) ==
            (← must (GenericInstantiationWorld.ofType initial.arena 16384 expected.typeId)))
            "source instantiated compatibility field differs"
      let (same,next) ← run state (queries.reprEqualUpToSeed fresh fresh)
      state := next
      check same "raw representation is not equal to itself"
      let (name,next) ← run state (queries.itemName fresh)
      state := next
      let some facts := node.compilerFacts.bind (·.adt) | throw (IO.userError "independent material ADT oracle absent")
      check (name == facts.itemName) "raw DefKey item symbol differs from compiler"
      let (hasNonnullAttribute,next) ← run state (queries.nonnullOptimizationGuaranteed fresh)
      state := next
      check (hasNonnullAttribute == facts.nonnullOptimizationGuaranteed) "raw nonnull attribute differs from compiler"
      if hasNonnullAttribute then nonnull := nonnull + 1
      let (identical,next) ← run state (LayoutCompat.identicalCTypes queries 256 fresh fresh)
      state := next
      check identical "actual structural compatibility rejected identical source ADT"
      count := count + 1
  check (count > 0) "no source ADTs tested"
  check (state.arena.materialTypes.isEmpty && state.arena.materialConstants.isEmpty && state.arena.materialPredicates.isEmpty)
    "compatibility acquired closed result prefixes"
  IO.println s!"PASS {count} empty-prefix ADT source dictionaries, instantiated fields, raw repr/name/nonnull ({nonnull} true), actual identicalCTypes"
