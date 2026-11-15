import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceCompilerInstances
import Miri.Input.SourcePhysical
open Lean Miri Miri.Input Miri.Frontend.Foundation

private def check (document : Document) (name : String) (expected : SourceMaterial.ItemRole)
    : IO Unit := do
  let world ← IO.ofExcept (compilerEntrySeed document)
  let some material := world.canonical.sourceMaterial | throw (IO.userError "typed declaration source absent")
  let [declaration] := (material.declarations.filter (·.path == name)).toList
    | throw (IO.userError "source declaration absent/ambiguous")
  unless declaration.role == expected do throw (IO.userError "wrong typed declaration role")
  let (world,definition) ← IO.ofExcept (SourceCompilerWorld.internDefinition world declaration.definition)
  let access : SourceCompilerWorld.Access SourceCompilerWorld.World := ⟨some,fun _ next => next⟩
  let (world,arguments) ← if declaration.parameters.isEmpty then pure (world,(#[] : Array MIR.GenericArg)) else do
    let (updated,unit) ← IO.ofExcept (SourcePhysical.intern world (.tuple #[]))
    let (updated,pointer) ← IO.ofExcept (SourcePhysical.intern updated (.functionPointer #[] (.tuple #[]) .Safe .Rust false))
    pure (updated,#[.Type pointer,.Type unit])
  match SourceCompilerInstances.itemInstance access definition arguments world with
  | .ok id updated =>
    unless expected == .ordinary do throw (IO.userError "special/unavailable function resolved as ordinary Item")
    unless (← IO.ofExcept (SourceCompilerWorld.node updated id)).kind == .identityOnly do
      throw (IO.userError "header-only resolution manufactured a body")
  | .error _ updated =>
    unless expected != .ordinary && updated.canonical.instances.size == world.canonical.instances.size do
      throw (IO.userError "ordinary header rejected or special role mutated instances")

def main (args : List String) : IO Unit := do
  let [stdPath,intrinsicPath,missingPath,conflictPath,bodyPath] := args | throw (IO.userError "expected fresh header-role sources")
  let std ← IO.ofExcept (Json.parse (← IO.FS.readFile stdPath) >>= decode)
  check std "std::sys::backtrace::__rust_begin_short_backtrace" .ordinary
  let intrinsic ← IO.ofExcept (Json.parse (← IO.FS.readFile intrinsicPath) >>= decode)
  check intrinsic "ordinary" .ordinary
  check intrinsic "breakpoint" .intrinsic
  let missing ← IO.ofExcept (Json.parse (← IO.FS.readFile missingPath) >>= decode)
  check missing "ordinary" .unavailable
  let conflict ← IO.ofExcept (Json.parse (← IO.FS.readFile conflictPath) >>= decode)
  match typedSourceMaterial conflict with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "conflicting body/header role accepted")
  let body ← IO.ofExcept (Json.parse (← IO.FS.readFile bodyPath) >>= decode)
  let material ← IO.ofExcept (typedSourceMaterial body)
  let [main] := (material.declarations.filter (·.path == "main")).toList
    | throw (IO.userError "body declaration absent")
  unless main.role == .ordinary do throw (IO.userError "known body role lost to incomplete header")
  IO.println "genuine Rust-ABI intrinsic header rejected; ordinary std header resolves through current World"
