import Miri.Input.DecodeMIR

open Miri.Input DecodeMIR

private def statementText := r#"{"variant":"Assign","place":{"local":1,"type":0,"projection":[]},"rvalue":{"kind":"Use","retag":{"kind":"no","performs_retag":false},"operand":{"kind":"Constant","constant":{"type":0,"span":0,"user_type_annotation":null,"constant":{"kind":"evaluated_const","value":{"kind":"scalar","size_bytes":1,"bits_unsigned":"7"}}}}}}"#

private def bodyText (locals : String) :=
  r#"{"phase":{"kind":"built"},"instance_id":0,"arg_count":0,"spread_arg":null,"locals":["# ++ locals ++
  r#"],"basic_blocks":[{"block":0,"is_cleanup":false,"statements":[{"source_info":0,"kind":0},{"source_info":0,"kind":0}],"terminator":{"source_info":0,"kind":{"variant":"Return"}}}],"source_scopes":[{"scope":0,"span":0,"parent":null,"inlined":null,"inlined_parent_scope":null}],"source_def_id":0,"span":0,"preamble_def_span":0,"backtrace_spans":0,"required_consts":[]}"#

private def local0 := r#"{"local":0,"type":0,"source_info":0}"#
private def local1 := r#"{"local":1,"type":0,"source_info":0}"#
private def context : Context := {
  typeCount := 1, allocationCount := 0, definitionCount := 1,
  typeConstantCount := 0, spanCount := 1, scalarSize := fun _ => some 1 }

def main : IO Unit := do
  let base : MIRParser.SharedPools := {sources := #[⟨0, 0⟩], backtraces := #[#[]]}
  let .ok statement := JsonReader.run (parseSharedStatement base) statementText
    | throw (IO.userError "shared statement parse failed")
  let pools := {base with statements := #[statement]}
  let decode (text : String) := JsonReader.run (parseBody "$body" (some pools)) text >>= resolveBody context
  let .ok body := decode (bodyText (local0 ++ "," ++ local1))
    | throw (IO.userError "shared statements did not decode in valid local context")
  let some facts := body.nodeFacts[0]? | throw (IO.userError "missing block facts")
  let some first := facts[0]? | throw (IO.userError "missing first statement facts")
  let some second := facts[1]? | throw (IO.userError "missing second statement facts")
  unless facts.size == 3 && first.places.size == 1 && second.places.size == 1 do
    throw (IO.userError "pooled statement facts were not replayed at each occurrence")
  unless !(decode (bodyText local0)).isOk do
    throw (IO.userError "shared statement escaped per-body local bounds")
  unless !(decode ((bodyText (local0 ++ "," ++ local1)).replace "\"source_info\":0" "\"source_info\":1")).isOk do
    throw (IO.userError "dangling pooled SourceInfo accepted")
  unless !(decode ((bodyText (local0 ++ "," ++ local1)).replace "\"backtrace_spans\":0" "\"backtrace_spans\":1")).isOk do
    throw (IO.userError "dangling pooled backtrace accepted")
  unless !(decode ((bodyText (local0 ++ "," ++ local1)).replace "\"kind\":0" "\"kind\":1")).isOk do
    throw (IO.userError "dangling pooled statement kind accepted")
  let badSpan := {pools with sources := #[⟨1, 0⟩]}
  unless !(JsonReader.run (parseBody "$body" (some badSpan)) (bodyText (local0 ++ "," ++ local1)) >>= resolveBody context).isOk do
    throw (IO.userError "pooled SourceInfo span escaped global bounds")
  let badScope := {pools with sources := #[⟨0, 1⟩]}
  unless !(JsonReader.run (parseBody "$body" (some badScope)) (bodyText (local0 ++ "," ++ local1)) >>= resolveBody context).isOk do
    throw (IO.userError "pooled SourceInfo scope escaped body bounds")
  let wrongWidth := {context with scalarSize := fun _ => some 2}
  unless !(JsonReader.run (parseBody "$body" (some pools)) (bodyText (local0 ++ "," ++ local1)) >>= resolveBody wrongWidth).isOk do
    throw (IO.userError "shared scalar width escaped compiler layout checks")
  IO.println "shared MIR pool checks: passed"
