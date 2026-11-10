import Miri.Input.DecodeMIR

open Miri Miri.Input

private def s (value : String) : String := Lean.Json.renderString value
private def obj (fields : List (String × String)) : String :=
  "{" ++ String.intercalate "," (fields.map fun (key,value) => s key ++ ":" ++ value) ++ "}"
private def arr (values : List String) : String := "[" ++ String.intercalate "," values ++ "]"
private def tag (kind : String) (fields : List (String × String) := []) := obj (("kind",s kind)::fields)
private def info := obj [("span","0"),("scope","0")]
private def place := obj [("local","0"),("type","0"),("projection","[]")]
private def operand := tag "Copy" [("place",place)]
private def node (value : String) := obj [("source_info",info),("kind",value)]
private def assignment (rvalue : String) := obj [("variant",s "Assign"),("place",place),("rvalue",rvalue)]
private def context : DecodeMIR.Context := {
  typeCount := 1, allocationCount := 0, definitionCount := 1,
  typeConstantCount := 0, spanCount := 1, scalarSizes := #[some 1] }
private def decode (statements : List String) (phase : String := tag "runtime" [("phase",s "optimized")]) := do
  let body := obj [
    ("def_id","0"),("phase",phase),("arg_count","0"),("spread_arg","null"),
    ("span","0"),("preamble_def_span","0"),("backtrace_spans","[]"),("required_consts","[]"),
    ("locals",arr [obj [("local","0"),("type","0"),("source_info",info)]]),
    ("source_scopes",arr [obj [("scope","0"),("parent","null"),("span","0"),("inlined","null"),("inlined_parent_scope","null")]]),
    ("basic_blocks",arr [obj [("block","0"),("is_cleanup","false"),("statements",arr (statements.map node)),
      ("terminator",node (obj [("variant",s "Return")]))]])]
  DecodeMIR.resolveBody context (← JsonReader.run (DecodeMIR.parseBody "$body") body)

private def rejects (result : Except String α) (message : String) : IO Unit :=
  unless !result.isOk do throw (IO.userError message)

def main : IO Unit := do
  let invalidOperator := assignment (tag "BinaryOp" [("operator",s "future_op")])
  match decode [invalidOperator,obj [("variant",s "FutureStatement")]] with
  | .ok _ => throw (IO.userError "invalid operator accepted")
  | .error message =>
    unless message.contains "binary operator" do throw (IO.userError s!"later statement masked first error: {message}")
  rejects (decode [] (tag "future_phase")) "unknown phase accepted"
  rejects (decode [] (tag "analysis" [("phase",s "optimized")])) "analysis/runtime stage mismatch accepted"
  rejects (decode [assignment (tag "Use" [("operand",operand),("retag",tag "yes" [("performs_retag","false")])])])
    "contradictory retag witness accepted"
  rejects (decode [assignment (tag "Use" [("operand",tag "RuntimeChecks" [("check",tag "overflow_checks" [("enabled","null")])]),
      ("retag",tag "no" [("performs_retag","false")])])]) "missing runtime-check witness accepted"
  rejects (decode [obj [("variant",s "Coverage"),("coverage",tag "point")]]) "missing coverage point kind accepted"
  let coverage (owner : String) := obj [("variant",s "Coverage"),("coverage",tag "point" [
    ("point_kind",s "expr"),("hir_id",obj [("owner_def_id",owner),("local_id","7")])])]
  rejects (decode [coverage (s "0:1")]) "text definition identity accepted"
  let .ok valid := decode [coverage "0"] | throw (IO.userError "valid source coverage rejected")
  let some block := valid.mir.basicBlocks[0]? | throw (IO.userError "missing decoded block")
  let some statement := block.statements[0]? | throw (IO.userError "missing decoded coverage")
  unless statement.kind == .Coverage (.Point .Expr ⟨0,7⟩) do
    throw (IO.userError "coverage identity was not decoded into final MIR")
  let projections := arr [tag "Deref", tag "Field" [("index","1")], tag "Index",
    tag "ConstantIndex" [("offset","2"),("min_length","4"),("from_end","true")],
    tag "Subslice" [("from","1"),("to","2"),("from_end","false")],
    tag "Downcast" [("name","null"),("variant_index","3")], tag "OpaqueCast", tag "UnwrapUnsafeBinder", tag "PhantomDeref"]
  let ascribe (base : String) := obj [("variant",s "AscribeUserType"),("place",place),
    ("user_type_projection",obj [("base_index",base),("projections",projections)]),("variance",tag "invariant")]
  let .ok projected := decode [ascribe "2"] | throw (IO.userError "valid user projections rejected")
  let some projectedBlock := projected.mir.basicBlocks[0]? | throw (IO.userError "missing projected block")
  let some projectedStatement := projectedBlock.statements[0]? | throw (IO.userError "missing projected statement")
  match projectedStatement.kind with
  | .AscribeUserType _ projection variance =>
    unless projection == ⟨2, #[.Deref,.Field 1,.Index,.ConstantIndex 2 4 true,.Subslice 1 2 false,
        .Downcast none 3,.OpaqueCast,.UnwrapUnsafeBinder,.PhantomDeref]⟩ && variance == .Invariant do
      throw (IO.userError "user projection identity or fields changed")
  | _ => throw (IO.userError "user projection did not become final MIR")
  rejects (decode [ascribe (s "not-an-index")]) "non-numeric user projection base accepted"
  rejects (decode [obj [("variant",s "Coverage"),("coverage",tag "future_coverage")]]) "unknown coverage accepted"
  IO.println "direct MIR decoder rejects malformed phases, witnesses, operators and coverage; preserves first error"
