import Miri.Input.MirDirectCall
import Miri.Input.GenericMaterialCodec

/-! Finite real rustc instantiated-MIR comparisons. These establish only the
ordinary callee substitution component, not instance/ABI/transfer resolution. -/
open Lean Miri.Input Miri.Input.GenericSubstitution
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error e => throw (IO.userError e)
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
private def readCallee (value : Json) : Except String MirDirectCall.Callee := do
  pure ⟨← GenericMaterialCodec.readDefinition (← value.getObjVal? "definition"),
    ← (← (← value.getObjVal? "arguments").getArr?).mapM (GenericMaterialCodec.readTerm 16384)⟩

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected pinned rustc call oracle JSON")
  let rows ← must ((← must (Json.parse (← IO.FS.readFile path))).getArr?)
  check (rows.size == 6) "expected six genuine rustc MIR instances"
  for row in rows do
    let source ← must (readCallee (← must (row.getObjVal? "source")))
    let arguments ← must ((← must ((← must (row.getObjVal? "arguments")).getArr?)).mapM
      (GenericMaterialCodec.readTerm 16384))
    let expected ← must (readCallee (← must (row.getObjVal? "expected")))
    let actual ← must (MirDirectCall.instantiateCallee 16384 arguments source)
    check (decide (actual = expected)) "callee substitution differs from pinned instantiated MIR"
    check (actual.definition == source.definition) "substitution changed the source callee definition"
    match MirDirectCall.instantiateCallee 16384 #[] source with
    | .ok _ => throw (IO.userError "missing caller arguments accepted")
    | .error _ => pure ()
    let template : MirDirectCall.Template := {
      callee := source, constantSpan := ⟨3⟩, source := ⟨⟨5⟩,2⟩,
      arguments := #[⟨⟨7⟩,.move 1⟩], destination := 0,
      target := some 4, unwind := .Unreachable, callSource := .Normal, functionSpan := ⟨11⟩ }
    let terminator ← must (MirDirectCall.instantiate 16384 arguments template fun callee => do
      unless callee = expected do throw "resolver received another raw callee"
      pure 19)
    let expectedTerminator : Miri.MIR.Terminator := ⟨⟨⟨5⟩,2⟩,
      .Call (.Constant ⟨⟨3⟩,none,.Val .ZeroSized 19⟩) #[⟨⟨7⟩,.Move ⟨1,#[]⟩⟩]
        ⟨0,#[]⟩ (some 4) .Unreachable .Normal ⟨11⟩⟩
    check (decide (terminator = expectedTerminator)) "call lowering lost source/operand/control metadata"
    match MirDirectCall.instantiate 16384 arguments template (fun _ => .error "unavailable exact function type") with
    | .ok _ => throw (IO.userError "missing function identity was silently accepted")
    | .error e => check (e == "unavailable exact function type") "function-type error was changed"
  IO.println "PASS six pinned ordinary direct-call MIR substitutions; metadata and failure propagation"
