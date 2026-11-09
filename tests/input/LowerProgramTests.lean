import Miri.Input.Decoder
import Miri.Input.LowerMIR

open Miri Input

private def must (value : Except String α) : IO α :=
  match value with | .ok v => pure v | .error e => throw (IO.userError e)

def main (args : List String) : IO Unit := do
  let path ← match args with | path :: _ => pure path | [] => throw (IO.userError "expected full compiler MIR fixture")
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let doc := decoded.document
  let some _target := doc.runtimeTargetDataLayout | throw (IO.userError "compiler target data layout evidence was lost")
  let program ← must (lowerProgram doc)
  unless program.roots.size == doc.bodyRoots.size do throw (IO.userError "root body lost")
  for (sourceBody, rootIndex) in doc.bodyRoots.toList.zipIdx do
    let dense ← must (program.rootDefinitionId rootIndex)
    unless dense == sourceBody.definitionId &&
        program.bundle.definitions[dense]? == doc.definitions[sourceBody.definitionId]? do
      throw (IO.userError "root frame definition lost its source identity")
    unless program.roots[rootIndex]? == some sourceBody.bodyId do
      throw (IO.userError "root body ID was rewritten")
  let expectedInstances := doc.instances.filter (·.bodyId.isSome)
  unless program.instances.size == expectedInstances.size do throw (IO.userError "instance body lost")
  unless program.bundle.bodies.size == doc.bodies.size do
    throw (IO.userError "body pool definitions were duplicated or discarded")
  for inst in expectedInstances do
    unless program.instances.contains (inst.id, inst.bodyId.getD 0) do
      throw (IO.userError "instance body ID was rewritten")
  for body in program.bundle.bodies do
    if let some sourceId := body.input.definitionId then
      let dense ← must body.ownDefinitionId
      unless dense == sourceId && program.bundle.definitions[dense]? == doc.definitions[sourceId]? do
        throw (IO.userError "body source identity is absent from shared definitions")
    unless body.definitions == program.bundle.definitions && body.typeConstants == program.bundle.typeConstants && body.spans == program.bundle.spans do
      throw (IO.userError "bundle body uses inconsistent compiler identity tables")
  let knownGeneric := doc.instances.find? (fun inst =>
    inst.defPath.any (·.endsWith "array_len") && inst.bodyId.isSome)
  if let some inst := knownGeneric then
    let some bodyId := inst.bodyId | throw (IO.userError "generic instance lost its body ID")
    let some generic := program.bundle.bodies[bodyId]? | throw (IO.userError "generic instance body is absent")
    unless generic.input.isPolymorphic == some false && generic.obligations.isEmpty do
      throw (IO.userError "concrete generic instantiation retained unresolved parameters")
  let knownTLS := doc.bodyRoots.find? (fun root => root.defPath.endsWith "read_tls")
  if let some root := knownTLS then
    let some tls := program.bundle.bodies[root.bodyId]? | throw (IO.userError "TLS root body is absent")
    unless tls.body.basicBlocks.any (fun block => block.statements.any fun statement =>
        match statement.kind with
        | .Assign _ (.ThreadLocalRef _) => true
        | _ => false) do
      throw (IO.userError "concrete TLS reference disappeared from lowered MIR")
  IO.println s!"program syntax lowered: {program.bundle.bodies.size} bodies, {program.roots.size} roots, {program.instances.size} instances, {program.promoted.size} promoted; global compiler tables and target evidence retained"
