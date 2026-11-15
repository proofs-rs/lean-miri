import Miri.Frontend.FoundationEntrySeed
import Miri.Input.CompilerCopy
import Miri.Input.SourcePhysical
open Lean Miri Miri.Input Miri.Interpreter Miri.Frontend.Foundation
-- Memory padding remains independent of World availability and evaluation state.
example (runtime : RuntimeMetadata) (access : SourceCompilerWorld.Access S)
    (debug : Bool) (layout : LocalLayout)
    (memory : layout.layout.backendRepr = .Memory (sized := sized)) :
    CompilerCopy.hasPaddingCurrent runtime access debug layout = pure true := by
  simp [CompilerCopy.hasPaddingCurrent, CompilerCopy.hasPadding, memory, pure, Except.pure]
  rfl

private def checked (r : Except String α) : IO α := match r with
| .ok a => pure a | .error e => throw (IO.userError e)
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "usage: genuine finite std source")
  let document ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
  let initial ← checked (compilerEntrySeed document)
  let some source := initial.canonical.sourceMaterial | throw (IO.userError "source absent")
  let some physical := source.physical | throw (IO.userError "physical source absent")
  let some evidence := initial.canonical.runtimeTargetDataLayout | throw (IO.userError "target absent")
  let target ← checked ((RuntimeMetadata.importTarget evidence).mapError reprStr)
  let runtime : RuntimeMetadata := ⟨initial.canonical,target⟩
  let access : SourceCompilerWorld.Access SourceCompilerWorld.World := ⟨some,fun _ w => w⟩
  let mut count := 0
  for (expression,reference) in physical.types.zipIdx do
    if let .reference .. := expression then
      if let .ok concrete := SourceTypes.instantiate physical #[] #[] reference >>= SourceTypes.eraseRegions then
        if let .ok (world,id) := SourcePhysical.intern initial concrete then
          let live : RuntimeMetadata := ⟨world.canonical,target⟩
          let layout ← checked ((live.lookup id).mapError reprStr)
          if let .ScalarPair .. := layout.layout.backendRepr then
            if id >= initial.canonical.types.size then
              match CompilerCopy.hasPadding runtime false layout with
              | .ok _ => throw (IO.userError "stale snapshot unexpectedly resolves new type")
              | .error _ => pure ()
              for debug in [false,true] do
                let expected ← checked ((CompilerCopy.hasPadding live debug layout).mapError reprStr)
                match CompilerCopy.hasPaddingCurrent runtime access debug layout world with
                | .ok actual after =>
                  unless actual == expected && after.canonical.types.size == world.canonical.types.size do
                    throw (IO.userError "live padding differs or changes canonical type pool")
                | .error e _ => throw (IO.userError (reprStr e))
              let absent : SourceCompilerWorld.Access SourceCompilerWorld.World := ⟨fun _ => none,fun _ w => w⟩
              match CompilerCopy.hasPaddingCurrent runtime absent false layout world with
              | .ok .. => throw (IO.userError "missing World accepted")
              | .error .. => pure ()
              count := count+1
  unless count > 0 do throw (IO.userError "no genuine newly demanded wide reference tested")
  IO.println s!"PASS {count} genuine live scalar-pair padding, stale snapshot reproduction, debug parity and absent World rejection"
