import Miri.Input.RuntimeProgram

/-! Diagnostic JSON requires no reflexivity certificate: both source views
are projections of one owner, including arbitrary diagnostic values. -/
open Miri.Input

example (owner : RuntimeProgram) : owner.runtime.source.raw = owner.program.input.raw := rfl
example (owner : RuntimeProgram) (raw : Lean.Json) :
    ({owner with input := {owner.input with raw}} : RuntimeProgram).runtime.source =
    ({owner with input := {owner.input with raw}} : RuntimeProgram).program.input := rfl

def main : IO Unit := IO.println "single source owner kernel checks PASS"
