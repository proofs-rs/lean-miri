import Miri.Input.Decoder
import Miri.Input.CompilerInstanceAbi

open Miri.Input GenericSubstitution WorldDeducedAbi

example : sourceNoDrop 32 (.atom .type "uint" "u8") = .ok true := by simp [sourceNoDrop]; rfl
example : sourceNoDrop 32 (.node .type "array" ""
    (.cons (.atom .type "bool" "") (.cons (.parameter .constant 0) .nil))) = .ok true := by decide
example : sourceNoDrop 32 (.node .type "tuple" ""
    (.cons (.atom .type "bool" "") (.cons (.atom .type "char" "") .nil))) = .ok true := by decide
example : sourceNoDrop 32 (.definition .type "adt" ⟨0,1⟩ .nil) = .ok false := by decide
example : sourceNoDrop 32 (.node .type "dynamic" "" .nil) = .ok false := by decide
example : sourceNoDrop 32 (.node .type "reference" "immutable"
    (.cons (.atom .region "erased" "") (.cons (.definition .type "adt" ⟨0,1⟩ .nil) .nil))) = .ok true := by decide
example : sourceNoDrop 32 (.node .type "raw_pointer" "mutable"
    (.cons (.definition .type "adt" ⟨0,1⟩ .nil) .nil)) = .ok true := by decide
example : sourceNoDrop 32 (.definition .type "function_definition" ⟨0,1⟩
    (.cons (.binder #[] (.node .aggregate "arguments" "" .nil)) .nil)) = .ok true := by decide
example : (sourceNoDrop 32 (.node .type "array" ""
    (.cons (.atom .type "uint" "u8") (.cons (.atom .type "bool" "") .nil)))).isOk = false := by decide
example : sourceNoDrop 32 (.atom .type "uint" "bogus") = .ok false := by simp [sourceNoDrop]; rfl
example : (sourceNoDrop 0 (.atom .type "bool" "")).isOk = false := by decide

private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

private def sameArgument (aWorld bWorld : TypeArena.World)
    (a b : Miri.ABI.ArgAbi TypeId) : Except String Bool := do
  pure ((← GenericInstantiationWorld.ofType aWorld 16384 a.layout.ty) ==
    (← GenericInstantiationWorld.ofType bWorld 16384 b.layout.ty) &&
    a.layout.layout == b.layout.layout && a.mode == b.mode)

private def sameAbi (aWorld bWorld : TypeArena.World)
    (a b : Miri.ABI.FnAbi TypeId) : Except String Bool := do
  unless a.args.size == b.args.size && a.conv == b.conv && a.cVariadic == b.cVariadic &&
      a.fixedCount == b.fixedCount && a.canUnwind == b.canUnwind &&
      (← sameArgument aWorld bWorld a.ret b.ret) do return false
  for (x,y) in a.args.zip b.args do
    unless ← sameArgument aWorld bWorld x y do return false
  pure true

def main (args : List String) : IO Unit := do
  let [candidatePath,oraclePath] := args | throw (IO.userError "expected DROP dependency candidate/oracle")
  let decoded := (← must (decodeJson (← IO.FS.readFile candidatePath))).document
  let document := {decoded with types := decoded.types.map (fun node =>
    {node with compilerFacts := node.compilerFacts.map (fun facts => {facts with booleanQueries := #[]})})}
  let oracle := (← must (decodeJson (← IO.FS.readFile oraclePath))).document
  let runtime ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let reference ← must ((RuntimeMetadata.ofDocument oracle).mapError toString)
  let world ← must ((RuntimeArrayTypes.create runtime).mapError reprStr)
  let oracleWorld ← must ((RuntimeArrayTypes.create reference).mapError reprStr)
  let prepared ← must (CompilerInstanceAbi.prepare runtime (← must (lowerProgram document)))
  let mut count := 0
  let mut covered := 0
  for row in oracle.queries.instanceAbis do
    let some node := oracle.instances[row.instanceId]? | throw (IO.userError "oracle instance missing")
    let .Item definition := node.instanceKind | continue
    let some decl := oracle.definitions[definition]? | continue
    unless (decl.rawPath.bind fun path => path.components.back?.bind (·.name)) == some "consume" do continue
    let arguments ← must (GenericInstantiationWorld.ofArguments oracleWorld.arena 16384 node.genericArgs)
    let sources ← must (document.instances.filterM fun candidate => do
      let key ← InstanceArena.Key.ofSource world.arena candidate.instanceKind candidate.genericArgs
      pure (key.definition == ⟨decl.crateIndex,decl.index⟩ &&
        (← GenericInstantiationWorld.ofArguments world.arena 16384 key.arguments) == arguments))
    let #[source] := sources | throw (IO.userError "candidate consume source not unique")
    let expected ← must (CallResolution.functionAbiId reference row.abiId)
    let some arg := expected.args[0]? | throw (IO.userError "consume argument absent")
    let term ← must (GenericInstantiationWorld.ofType oracleWorld.arena 16384 arg.layout.ty)
    let rawSupported ← must (sourceNoDrop 16384 term)
    let result := (WorldInstanceAbi.construct source.id #[]).run world
    if rawSupported then
      let (actual,after) ← must result
      unless ← must (sameAbi after.arena oracleWorld.arena actual expected) do
        throw (IO.userError "source noDrop attributes differ from actual rustc")
      if document.queries.instanceAbis.any (·.instanceId == source.id) then
        throw (IO.userError "covered noDrop dependency retained an eager ABI answer")
      let some actualArg := actual.args[0]? | throw (IO.userError "actual consume argument absent")
      let .Indirect attrs _ _ := actualArg.mode | throw (IO.userError "consume did not pass indirectly")
      unless attrs.regular == 703 do throw (IO.userError "noDrop consume argument lacks exact703 attributes")
      let invalid := {actualArg with layout := {actualArg.layout with ty := world.arena.typeCount + 1000}}
      if ((applyUsage 1 invalid).run world).isOk then
        throw (IO.userError "DROP dependency accepted a missing raw type")
      let (unchanged,_) ← must ((applyUsage 13 invalid).run world)
      unless unchanged == invalid do throw (IO.userError "MUTATE|CAPTURE did not short circuit DROP dependency")
      covered := covered + 1
    else
      let .definition .type "adt" identity _ := term | throw (IO.userError "unexpected source noDrop residual type")
      let declarations := oracle.definitions.filter fun definition =>
        definition.crateIndex == identity.crateIndex && definition.index == identity.index
      let #[declaration] := declarations | throw (IO.userError "residual ADT declaration is not unique")
      let name := declaration.rawPath.bind fun path => path.components.back?.bind (·.name)
      let expectedBits ← match name with
        | some "Plain" => pure 703
        | some "Droppy" => pure 670
        | _ => throw (IO.userError "unexpected residual ADT source declaration")
      let .Indirect attributes _ _ := arg.mode | throw (IO.userError "residual ADT argument is not indirect")
      unless attributes.regular == expectedBits do throw (IO.userError "actual drop-false/drop-true oracle distinction was lost")
      match result with
      | .error error => do
        unless error.contains "source-derived needsDrop" do
          throw (IO.userError s!"unexpected raw DROP residual: {error}")
      | .ok _ => throw (IO.userError "unknown ADT acquired a noDrop result")
      unless document.queries.instanceAbis.any (·.instanceId == source.id) do
        throw (IO.userError "unknown DROP dependency lost its exact material ABI")
    let (actual,after) ← must ((CompilerInstanceAbi.abiOfInstanceInWorld prepared source.id #[]).run world)
    unless ← must (sameAbi after.arena oracleWorld.arena actual expected) do
      throw (IO.userError "DROP-aware provider or retained material residual differs from rustc")
    count := count + 1
  unless count == 3 && covered == 1 do throw (IO.userError s!"wrong DROP coverage {covered}/{count}")
  IO.println "PASS source noDrop consume703 with copied booleans removed, actual drop-false/drop-true ADT exact residuals, malformed and dependency short-circuit controls"
