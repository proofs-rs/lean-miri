import MiriTests.Input.LegacyFixture
import Miri.Input.CompilerVirtualFacts
import Miri.Input.CompilerLifecycle
import Miri.Input.CompilerFactAdapters
import Miri.Input.Decoder
import Miri.Input.LowerMIR

open Lean Miri.Input

private def must (value : Except String α) : IO α :=
  match value with | .ok result => pure result | .error message => throw (IO.userError message)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def tables (program : LoweredProgram) :=
  (program.bundle.spans, program.bundle.definitions, program.bundle.typeConstants)

private def materialBody (program : LoweredProgram) (index : Nat) : Except String Body := do
  let initial ← TypeArena.World.ofDocument program.input
  let (source,arena) ← (SourceMir.resolveBody program.input index).run initial
  unless arena.constructedTypes.isEmpty && arena.constructedConstants.isEmpty do
    throw "test material mutation cannot discard execution-owned constructor identities"
  let some seed := program.input.bodies[index]? | throw "test body seed absent"
  pure {toBodyCore := source, promotedBodies := seed.promotedBodies}

private def checkInlineScopes (program : LoweredProgram) : IO Unit := do
  -- Scope preparation rejects contradictions even when nobody queries that instance.
  let body ← must (materialBody program 0)
  let some callee := program.input.instances[0]? |
    throw (IO.userError "fixture has no canonical inlinecallee instance")
  check (!program.compilerTables.spans.isEmpty) "fixture has no inline callsite span"
  let scope (id : Nat) (track : Bool) : SourceScope := {
    id, parent := none, spanId := 0, inlinedParent := none
    inlined := some ⟨callee.id, 0, track⟩ }
  let withScopes (scopes : Array SourceScope) := {
    program with input := { program.input with bodies := #[.material {
      body with sourceScopes := scopes }] } }
  let equal ← must (CompilerScopes.prepare (withScopes #[scope 0 true, scope 1 true]))
  check (CompilerVirtualFacts.inlineAttribute equal callee.id == some true)
    "identical inlinecallee attribute duplicates changed the answer"
  check (CompilerVirtualFacts.inlineAttribute equal (program.input.instances.size + 1) == none)
    "missing inlinecallee attribute did not retain the base-query fallback"
  check (CompilerScopes.inlineRequiresCallerLocation equal callee.id == .ok true)
    "required inlinecallee attribute differs from the indexed answer"
  match CompilerScopes.prepare (withScopes #[scope 0 true, scope 1 false]) with
  | .error error =>
    check (error == "conflicting full-instance inlinecallee attributes")
      "contradictory unused inlinecallee failed for an unrelated reason"
  | .ok _ => throw (IO.userError "contradictory unused inlinecallee passed table construction")
  let acrossBodies := { program with input := { program.input with bodies := #[
    .material { body with sourceScopes := #[scope 0 true] },
    .material { body with sourceScopes := #[scope 0 false] }] } }
  check (!(CompilerScopes.prepare acrossBodies).isOk)
    "contradictory inlinecallee attributes in distinct bodies passed construction"
  let erroneous ← must (CompilerScopes.prepare (withScopes #[scope 9 false, scope 1 true]))
  check (CompilerVirtualFacts.inlineAttribute erroneous callee.id == some true)
    "failed scope entry changed the valid inlinecallee evidence"
  check (!(CompilerScopes.sourceScope erroneous 0 0).isOk)
    "failed scope entry lost its deferred source-scope error"
  IO.println "inline attribute indexing rejects contradictions during table construction"

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected exporter MIR input")
  let input ← must (decodeFixture (← IO.FS.readFile path))
  let program ← must (lowerProgram input.document)
  checkInlineScopes program
  let prepared := CompilerLifecycle.prepare program
  check (tables prepared.program == tables program) "lifecycle preparation changed compiler pool IDs"
  check (prepared.entries.size == program.bodyCount) "lifecycle entries changed body pool indexing"
  let index := 0
  let body ← must (materialBody program index)
  check (body.instanceId < program.input.instances.size) "resolved body instance is absent"
  let invalidBody := { body with preambleDefSpanId := program.input.spans.size }
  let invalid := { program with input := { program.input with bodies := program.input.bodies.set! index (.material invalidBody) } }
  let rejected := CompilerLifecycle.prepare invalid
  let some rejectedEntry := rejected.entries[index]? | throw (IO.userError "missing lifecycle entry")
  check (!rejectedEntry.preamble.isOk) "invalid source span became lifecycle evidence"
  check (tables rejected.program == tables program) "failed lifecycle preparation changed compiler pools"
  let invalidBody := { body with instanceId := program.input.instances.size }
  let invalid := { program with input := { program.input with bodies := program.input.bodies.set! index (.material invalidBody) } }
  let rejected := CompilerLifecycle.prepare invalid
  let some entry := rejected.entries[index]? | throw (IO.userError "missing lifecycle entry")
  check (!entry.callee.isOk) "out of bounds body instance was accepted"
  let runtime ← must ((RuntimeMetadata.ofDocument input.document).mapError toString)
  let context ← must (CompilerFacts.ofProgram runtime program)
  let casts ← must (CompilerFactAdapters.prepare context)
  check (casts.castTypes.size == input.document.types.size) "cast classification changed dense type indexing"
  let mut classifiedCases := 0
  let mut deferredCases := 0
  for node in input.document.types do
    let actual := CompilerFactAdapters.castTypeInfo casts node.id
    let expected : Option Miri.Interpreter.CastTypeInfo := match node.shape with
      | .bool => some .boolean
      | .char => some .character
      | .int (.known kind) | .uint (.known kind) => some (.integer kind)
      | .rawPointer pointee _ => some (.rawPointer pointee)
      | .reference pointee .. => some (.reference pointee)
      | .functionDefinition definition args .. => some (.fnDefinition definition args)
      | .slice element => some (.slice element)
      | .tuple elements => some (.tuple elements)
      | _ => none
    if let some expected := expected then
      check (actual == .ok expected) s!"cast type {node.id} changed its source classification"
      classifiedCases := classifiedCases + 1
    match node.shape with
    | .never | .str =>
      check (actual == .error "type kind is outside the cast operand domain")
        s!"cast type {node.id} lost its deferred domain error"
      deferredCases := deferredCases + 1
    | _ => pure ()
  check (classifiedCases > 0 && deferredCases > 0) "cast fixture must exercise classification and deferred errors"
  -- Constructor IDs can now extend material data; use the actual interner so
  -- existing canonical constructors retain their source IDs.
  let initialTypes ← must (TypeArena.World.ofDocument input.document)
  let (pointerId,typeArena) ← must ((TypeArena.World.internType (.rawPointer 0 .Mut)).run initialTypes)
  let (pointerInfo,retained) ← must ((CompilerFactAdapters.castTypeInfoInWorld casts pointerId).run typeArena)
  check (pointerInfo == .rawPointer 0 && retained.typeCount == typeArena.typeCount)
    "lazy cast type constructor was treated as a missing material identity"
  let missingMaterialEntry := {casts with castTypes := #[]}
  check (CompilerFactAdapters.castTypeInfo missingMaterialEntry 0 ==
    .error "compiler cast type identity missing") "missing material cast classification was accepted"
  IO.println "dense cast classifications preserve source identities and deferred domain errors"
  IO.println "resolved lifecycle preparation retains typed IDs and rejects invalid source metadata"
