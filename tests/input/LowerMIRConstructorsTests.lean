import Miri.Input.DecodeMIR

open Miri Input

private def must (value : Except String α) : IO α :=
  match value with | .ok v => pure v | .error e => throw (IO.userError e)

private def s (x : String) : String := "\"" ++ x ++ "\""
private def n (x : Nat) : String := toString x
private def b (x : Bool) : String := if x then "true" else "false"
private def nil : String := "null"
private def obj (fs : List (String × String)) : String :=
  "{" ++ String.intercalate "," (fs.map fun (k,v) => s k ++ ":" ++ v) ++ "}"
private def arr (xs : List String) : String := "[" ++ String.intercalate "," xs ++ "]"
private def tagged (kind : String) (fs : List (String × String) := []) : String := obj (("kind", s kind) :: fs)
private def pl : String := obj [("local", n 0), ("type", n 0), ("projection", arr [])]
private def op : String := tagged "Copy" [("place", pl)]
private def defRef : String := n 0
private def unwind : String := tagged "Continue"
private def tc (_ : Nat) : String := n 0
private def tlsGlobalInfo : String := obj [
  ("nested", b false), ("size_bytes", n 0), ("align_bytes", n 1),
  ("mutability", s "immutable"), ("is_static", b true),
  ("is_foreign_item", b false), ("thread_local", b true)]
private def tlsInitializer : String := obj [("allocation", obj [
  ("size_bytes", n 0), ("align_bytes", n 1), ("mutability", s "immutable"),
  ("byte_image_id", n 0), ("initialization_ranges", arr []), ("relocations", arr [])])]
private def constant (ty span : Nat) : String := obj [
  ("type", n ty), ("user_type_annotation", nil), ("span", n span),
  ("constant", tagged "evaluated_const" [("value", tagged "scalar" [("bits_unsigned", s "1"), ("size_bytes", n 1)])])]

private def rvalues (ty : Nat) : Array (String × Array (String × String)) := #[
  ("Use", #[("operand", op), ("retag", tagged "no" [("performs_retag", b false)])]),
  ("Repeat", #[("operand", op), ("count", tc ty)]),
  ("Ref", #[("region", tagged "late_parameter" [("scope_def_id", defRef), ("parameter", tagged "named_anonymous" [("index", n 8), ("name", s "r")])]), ("borrow_kind", tagged "shared"), ("place", pl)]),
  ("ThreadLocalRef", #[("def_id", defRef), ("global_info", tlsGlobalInfo),
    ("initializer", tlsInitializer)]),
  ("RawPtr", #[("pointer_kind", tagged "metadata_only"), ("place", pl)]),
  ("Cast", #[("cast_kind", tagged "PointerCoercion" [("coercion", tagged "ClosureFnPointer" [("safety", tagged "unsafe")]), ("source", tagged "as_cast")]), ("operand", op), ("target_type", n ty)]),
  ("BinaryOp", #[("operator", tagged "add"), ("left", op), ("right", op)]),
  ("UnaryOp", #[("operator", tagged "not"), ("operand", op)]),
  ("Discriminant", #[("place", pl)]),
  ("Aggregate", #[("aggregate_kind", tagged "Adt" [("def_id", defRef), ("variant_index", n 2), ("generic_args", arr [tagged "const" [("value", tc ty)]]), ("user_type_annotation", tagged "annotation_ref" [("index", n 1)]), ("active_union_field", n 4)]), ("operands", arr [op])]),
  ("CopyForDeref", #[("place", pl)]),
  ("WrapUnsafeBinder", #[("operand", op), ("type", n ty)]),
  ("Reborrow", #[("type", n ty), ("mutability", tagged "mutable"), ("place", pl)])]

private def statements (ty : Nat) : Array (String × Array (String × String)) := #[
  ("Assign", #[("place", pl), ("rvalue", tagged "Repeat" [("operand", op), ("count", tc ty)])]),
  ("FakeRead", #[("cause", tagged "matched_place" [("hoisted_from", defRef)]), ("place", pl)]),
  ("SetDiscriminant", #[("place", pl), ("variant_index", n 2)]),
  ("StorageLive", #[("local", n 0)]), ("StorageDead", #[("local", n 0)]),
  ("PlaceMention", #[("place", pl)]),
  ("AscribeUserType", #[("place", pl), ("user_type_projection", obj [("base_index", n 2), ("projections", arr [tagged "Deref", tagged "Field" [("index", n 1)], tagged "Index", tagged "ConstantIndex" [("offset", n 1), ("min_length", n 3), ("from_end", b false)], tagged "Subslice" [("from", n 1), ("to", n 2), ("from_end", b true)], tagged "Downcast" [("name", s "V"), ("variant_index", n 2)], tagged "OpaqueCast", tagged "UnwrapUnsafeBinder", tagged "PhantomDeref"])]), ("variance", tagged "contravariant")]),
  ("Coverage", #[("coverage", tagged "point" [("point_kind", s "function_end"), ("hir_id", obj [("owner_def_id", defRef), ("local_id", n 3)])])]),
  ("Intrinsic", #[("intrinsic", s "CopyNonOverlapping"), ("src", op), ("dst", op), ("count", op)]),
  ("ConstEvalCounter", #[]), ("Nop", #[]),
  ("BackwardIncompatibleDropHint", #[("place", pl), ("reason", tagged "edition_2024")])]

private def asm (ty : Nat) (span : Nat) : Array (String × String) := #[
  ("asm_macro", s "asm"), ("template", arr [tagged "string" [("text", s "x")], tagged "placeholder" [("operand_index", n 0), ("modifier", s "e"), ("span", n span)]]),
  ("operands", arr [
    tagged "in" [("register", tagged "register_class" [("arch", s "X86_64"), ("name", s "reg")]), ("value", op)],
    tagged "out" [("register", tagged "register" [("arch", s "X86_64"), ("name", s "rax")]), ("late", b true), ("place", pl)],
    tagged "inout" [("register", tagged "register_class" [("arch", s "X86_64"), ("name", s "reg")]), ("late", b false), ("input", op), ("output", nil)],
    tagged "const" [("value", constant ty span)], tagged "sym_fn" [("value", constant ty span)],
    tagged "sym_static" [("def_id", defRef)], tagged "label" [("target_index", n 0)]]),
  ("options", obj ((["pure", "nomem", "readonly", "preserves_flags", "noreturn", "nostack", "att_syntax", "raw", "may_unwind"]).map (fun key => (key, b false)))),
  ("line_spans", arr [n span]), ("targets", arr [n 0]), ("unwind", unwind)]

private def terms (ty : Nat) (span : Nat) : Array (String × Array (String × String)) := #[
  ("Goto", #[("target", n 0), ("loop_hints", arr [tagged "Hint", tagged "Full", tagged "Never", tagged "Count" [("count", n 7)]])]),
  ("SwitchInt", #[("discriminant", op), ("targets", arr [obj [("value", s "18446744073709551615"), ("target", n 0)]]), ("otherwise", n 0)]),
  ("UnwindResume", #[]), ("UnwindTerminate", #[("reason", tagged "in_cleanup")]), ("Return", #[]), ("Unreachable", #[]),
  ("Drop", #[("place", pl), ("target", n 0), ("unwind", tagged "Terminate" [("reason", tagged "abi")]), ("replace", b true), ("async_drop", n 0)]),
  ("Call", #[("function", op), ("args", arr [obj [("operand", op), ("span", n span)]]), ("destination", pl), ("target", n 0), ("unwind", tagged "Cleanup" [("target", n 0)]), ("call_source", tagged "normal_call"), ("function_span", n span)]),
  ("TailCall", #[("function", op), ("args", arr []), ("function_span", n span)]),
  ("Assert", #[("condition", op), ("expected", b false), ("message", tagged "ResumedAfterDrop" [("coroutine_kind", tagged "desugared" [("desugaring", s "async_gen"), ("source", s "closure")])]), ("target", n 0), ("unwind", unwind)]),
  ("Yield", #[("value", op), ("resume", n 0), ("resume_arg", pl), ("drop", n 0)]), ("CoroutineDrop", #[]),
  ("FalseEdge", #[("real_target", n 0), ("imaginary_target", n 0)]),
  ("FalseUnwind", #[("real_target", n 0), ("unwind", tagged "Unreachable")]), ("InlineAsm", asm ty span)]

private def source := obj [("span",n 0),("scope",n 0)]
private def node (kind : String) := obj [("source_info",source),("kind",kind)]
private def ret := obj [("variant",s "Return")]
private def body (statements : List String) (term : String) := obj [
  ("source_def_id",n 0),("instance_id",n 0),("phase",tagged "built"),("arg_count",n 0),("spread_arg",nil),
  ("span",n 0),("preamble_def_span",n 0),("backtrace_spans",arr []),("required_consts",arr []),
  ("locals",arr [obj [("local",n 0),("type",n 0),("source_info",source)]]),
  ("source_scopes",arr [obj [("scope",n 0),("parent",nil),("span",n 0),("inlined",nil),("inlined_parent_scope",nil)]]),
  ("basic_blocks",arr [obj [("block",n 0),("is_cleanup",b false),("statements",arr (statements.map node)),("terminator",node term)]])]
private def context : DecodeMIR.Context := {
  typeCount := 1,allocationCount := 0,definitionCount := 4,typeConstantCount := 1,spanCount := 1,
  scalarSize := fun id => if id == 0 then some 1 else none }
private def decode (statements : List String) (term : String) := do
  DecodeMIR.resolveBody context (← JsonReader.run (DecodeMIR.parseBody "bodies[0]") (body statements term))

def main (_args : List String) : IO Unit := do
  for (kind, fs) in rvalues 0 do
    let value ← must (decode [obj [("variant",s "Assign"),("place",pl),("rvalue",tagged kind fs.toList)]] ret)
    unless value.mir.basicBlocks.size == 1 do throw (IO.userError "missing rvalue block")
  for (kind, fs) in statements 0 do
    let _ ← must (decode [obj (("variant",s kind)::fs.toList)] ret)
  for (kind, fs) in terms 0 0 do
    let fs := if kind == "Call" || kind == "TailCall" then fs.push ("resolution",tagged "resolved_instance" [("instance_id",n 0),("function_type",n 0),("fn_abi",n 0)]) else fs
    let _ ← must (decode [] (obj (("variant",s kind)::fs.toList)))
  unless (decode [obj [("variant",s "FutureStatement")]] ret).isOk == false do
    throw (IO.userError "unknown statement accepted")
  unless (decode [] (obj [("variant",s "FutureTerminator")])).isOk == false do
    throw (IO.userError "unknown terminator accepted")
  let mkClosure (other : Nat) := obj [("variant",s "Assign"),("place",pl),
    ("rvalue",tagged "Aggregate" [("aggregate_kind",tagged "Closure" [("def_id",n other),("generic_args",arr [tagged "const" [("value",n 0)]])]),("operands",arr [])])]
  let a ← must (decode [mkClosure 2] ret)
  let b ← must (decode [mkClosure 1] ret)
  let closureRef (body : Body) := do
    let block ← body.mir.basicBlocks[0]?
    let statement ← block.statements[0]?
    match statement.kind with
    | .Assign _ (.Aggregate (.Closure defId #[.Const constId]) _) => some (defId,constId)
    | _ => none
  unless closureRef a == some (2,0) && closureRef b == some (1,0) do
    throw (IO.userError "cross-body compiler IDs changed")
  IO.println "all 13 rvalue, 12 statement, 15 terminator variants decoded directly to MIR"
