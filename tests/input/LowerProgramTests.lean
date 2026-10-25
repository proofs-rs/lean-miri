import Miri.Input.Decoder
import Miri.Input.LowerMIR

open Miri Input

private def must (value : Except String α) : IO α :=
  match value with | .ok v => pure v | .error e => throw (IO.userError e)

def main (args : List String) : IO Unit := do
  let path ← match args with | path :: _ => pure path | [] => throw (IO.userError "expected full compiler MIR fixture")
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let doc := decoded.document
  let some target := doc.runtimeTargetDataLayout | throw (IO.userError "compiler target data layout evidence was lost")
  unless target.status == .supported do throw (IO.userError "target data layout query was incomplete")
  let program ← must (lowerProgram doc)
  unless program.roots.size == doc.bodies.size do throw (IO.userError "root body lost")
  for (sourceBody, rootIndex) in doc.bodies.toList.zipIdx do
    let some sourceId := sourceBody.definitionId | throw (IO.userError "compiler fixture root has no source identity")
    let dense ← must (program.rootDefinitionId rootIndex)
    unless program.bundle.definitions[dense]? == some sourceId do
      throw (IO.userError "root frame definition lost its crate-qualified source identity")
  let expectedInstances := doc.instances.filter (·.body.isSome)
  unless program.instances.size == expectedInstances.size do throw (IO.userError "instance body lost")
  let expectedPromoted := doc.bodies.foldl (fun count body => count + (body.promotedBodies.filter (·.body.isSome)).size) 0
  let expectedPromoted := doc.instances.foldl (fun count inst =>
    match inst.body with
    | none => count
    | some body =>
      let children := if body.promotedBodies.isEmpty then inst.promotedBodies else body.promotedBodies
      count + (children.filter (·.body.isSome)).size) expectedPromoted
  unless program.promoted.size == expectedPromoted && program.bundle.bodies.size == program.roots.size + program.instances.size + expectedPromoted do
    throw (IO.userError "promoted bodies or exact graph body count lost")
  unless program.input.obligations == doc.obligations do throw (IO.userError "document execution obligations disappeared")
  for body in program.bundle.bodies do
    if let some sourceId := body.input.definitionId then
      let dense ← must body.ownDefinitionId
      unless program.bundle.definitions[dense]? == some sourceId do
        throw (IO.userError "body source identity is absent from shared definitions")
    unless body.definitions == program.bundle.definitions && body.typeConstants == program.bundle.typeConstants && body.spans == program.bundle.spans do
      throw (IO.userError "bundle body uses inconsistent compiler identity tables")
  let knownGeneric := program.bundle.bodies.find? (fun body => body.input.defPath.endsWith "array_len")
  if let some generic := knownGeneric then
    unless !generic.obligations.isEmpty do throw (IO.userError "generic const parameter obligation disappeared")
  let knownTLS := program.bundle.bodies.find? (fun body => body.input.defPath.endsWith "read_tls")
  if let some tls := knownTLS then
    unless tls.body.basicBlocks.any (fun block => block.statements.any fun statement =>
        match statement.kind with
        | .Assign _ (.ThreadLocalRef _) => true
        | _ => false) do
      throw (IO.userError "concrete TLS reference disappeared from lowered MIR")
  IO.println s!"program syntax lowered: {program.bundle.bodies.size} bodies, {program.roots.size} roots, {program.instances.size} instances, {program.promoted.size} promoted; global compiler tables and target evidence retained"
