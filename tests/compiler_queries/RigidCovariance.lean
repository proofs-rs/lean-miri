import Miri.Input.Decoder
import Miri.Input.CompilerCovariance
open Miri.Input
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected actual std guest document")
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let world ← must (TypeArena.World.ofDocument document)
  unless (← must (world.shapeKind 1071)) == .adt && (← must (world.shapeKind 4)) == .uint do
    throw (IO.userError "actual failing source pair changed constructor heads")
  let empty := CompilerQueryIndices.covariance #[]
  let relation := CompilerCovariance.relationInWorld empty
  unless (relation world 1071 4 == .ok false) && (relation world 4 1071 == .ok false) &&
      (relation world 1071 1071 == .ok true) && (relation world 4 4 == .ok true) do
    throw (IO.userError "rigid negative relation differs from fresh rustc oracle")
  let (tuple,retained) ← must ((TypeArena.World.internType (.tuple (Array.replicate 37 4))).run world)
  unless relation retained tuple 4 == .ok false do
    throw (IO.userError "new constructed tuple did not use current execution world")
  if (relation world tuple 4).isOk then
    throw (IO.userError "constructed identity leaked into initial world")
  for unknown in [TypeShapeKind.alias,.patternType,.unsafeBinder] do
    unless !CompilerCovariance.rigidMismatch unknown .uint &&
        !CompilerCovariance.rigidMismatch .uint unknown do
      throw (IO.userError "unported normalization/binder relation was guessed")
  unless !CompilerCovariance.rigidMismatch .uint .uint do
    throw (IO.userError "same-head variance was guessed")
  IO.println "PASS actual std rigid mismatch matches rustc oracle; constructed IDs retained; aliases/binders deferred"
