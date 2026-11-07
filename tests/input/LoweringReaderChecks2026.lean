import Miri.Input.LowerMIR

open Lean Miri.Input

private def must (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def checkSourcePaths (program : LoweredProgram) : IO Unit := do
  for lowered in program.bundle.bodies do
    let input := lowered.input
    match input.context with
    | .raw => throw (IO.userError s!"body lost checked references: {input.sourcePath}")
    | .checked _ shape =>
      unless input.locals.size == shape.locals && input.blocks.size == shape.blocks do
        throw (IO.userError s!"body shape differs from its arrays: {input.sourcePath}")
    unless input.sourcePath.startsWith "$." &&
        jsonAtPath program.input.raw input.sourcePath == some input.payload do
      throw (IO.userError s!"body source path does not resolve: {input.sourcePath}")

private def compare (full runtime : LoweredProgram) : IO Unit := do
  checkSourcePaths full
  checkSourcePaths runtime
  unless full.roots == runtime.roots && full.instances == runtime.instances &&
      full.promoted == runtime.promoted &&
      full.bundle.spans == runtime.bundle.spans &&
      full.bundle.definitions == runtime.bundle.definitions &&
      full.bundle.typeConstants == runtime.bundle.typeConstants &&
      full.bundle.bodies.size == runtime.bundle.bodies.size do
    throw (IO.userError "full/runtime body indices or shared tables differ")
  for (a, b) in full.bundle.bodies.zip runtime.bundle.bodies do
    unless a.input.sourcePath == b.input.sourcePath && a.body == b.body &&
        a.obligations == b.obligations do
      throw (IO.userError s!"full/runtime MIR or obligations differ: {a.input.sourcePath}")

def main (args : List String) : IO Unit := do
  let path := args.headD "examples/empty_function/input.json"
  let text ← IO.FS.readFile path
  let full ← must (decodeJson text)
  let runtime ← must (decodeRuntimeJson text)
  let a ← must (lowerCoreProgram full.document.toCore)
  let b ← must (lowerCoreProgram runtime.document)
  compare a b
  IO.println s!"LoweringReaderChecks: {a.bundle.bodies.size} full/runtime root/instance/promoted bodies checked"
