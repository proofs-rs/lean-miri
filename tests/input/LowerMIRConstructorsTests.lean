import Miri.Input.Decoder
import Miri.Input.LowerMIR

open Miri Input

private def must (value : Except String α) : IO α :=
  match value with | .ok v => pure v | .error e => throw (IO.userError e)

private partial def containsProbe : TypedValue → Bool
  | .array values => values.any containsProbe
  | .object fields => fields.any fun (key, value) =>
      (key == "kind" && value == .scalar (.str "symbolic_vtable_allocation")) || containsProbe value
  | .statement _ _ fields | .terminator _ _ fields | .rvalue _ _ fields
  | .operand _ _ fields | .projection _ fields | .enumTag _ _ fields =>
      fields.any fun (_, value) => containsProbe value
  | _ => false

private partial def mutateProbeStatus : TypedValue → TypedValue
  | .array values => .array (values.map mutateProbeStatus)
  | .object fields =>
      let isProbe := fields.any fun (key, value) =>
        key == "kind" && value == .scalar (.str "symbolic_vtable_allocation")
      .object (fields.map fun (key, value) =>
        if isProbe && key == "status" then (key, .scalar (.str "unsupported"))
        else (key, mutateProbeStatus value))
  | .statement variant status fields => .statement variant status (fields.map fun (key, value) => (key, mutateProbeStatus value))
  | .terminator variant status fields => .terminator variant status (fields.map fun (key, value) => (key, mutateProbeStatus value))
  | .rvalue variant status fields => .rvalue variant status (fields.map fun (key, value) => (key, mutateProbeStatus value))
  | .operand variant status fields => .operand variant status (fields.map fun (key, value) => (key, mutateProbeStatus value))
  | .projection variant fields => .projection variant (fields.map fun (key, value) => (key, mutateProbeStatus value))
  | .enumTag category tag fields => .enumTag category tag (fields.map fun (key, value) => (key, mutateProbeStatus value))
  | value => value

private def obj (fs : List (String × TypedValue)) : TypedValue := .object fs.toArray
private def n (x : Nat) : TypedValue := .scalar (Lean.toJson x)
private def s (x : String) : TypedValue := .scalar (.str x)
private def b (x : Bool) : TypedValue := .scalar (.bool x)
private def nil : TypedValue := .scalar .null
private def arr (xs : List TypedValue) : TypedValue := .array xs.toArray
private def tagged (kind : String) (fs : List (String × TypedValue) := []) : TypedValue := obj (("kind", s kind) :: fs)
private def pl : TypedValue := obj [("local", .localRef 0), ("projection", arr [])]
private def op : TypedValue := .operand .copy .supported #[("place", pl)]
private def defRef : TypedValue := obj [("crate", n 2), ("index", n 7)]
private def unwind : TypedValue := tagged "Continue"
private def tc (ty : Nat) : TypedValue := tagged "value" [("type", .typeRef ty), ("value", tagged "leaf" [("size_bytes", n 4), ("bits_unsigned", s "3")])]

private def constant (ty : Nat) (span : SourceSpanData) : TypedValue := obj [
  ("type", .typeRef ty), ("user_type_annotation", nil), ("span", .sourceSpan span),
  ("constant", obj [("source", tagged "already_evaluated"), ("value", tagged "scalar" [("bits_unsigned", s "1")])])]

private def rvalues (ty : Nat) : Array (RvalueVariant × Array (String × TypedValue)) := #[
  (.use, #[("operand", op), ("retag", tagged "no")]),
  (.repeat, #[("operand", op), ("count", tc ty)]),
  (.ref, #[("region", tagged "late_parameter" [("scope_def_id", defRef), ("parameter", tagged "named_anonymous" [("index", n 8), ("name", s "r")])]), ("borrow_kind", tagged "shared"), ("place", pl)]),
  (.threadLocalRef, #[("def_id", defRef)]),
  (.rawPtr, #[("pointer_kind", tagged "metadata_only"), ("place", pl)]),
  (.cast, #[("cast_kind", tagged "PointerCoercion" [("coercion", tagged "ClosureFnPointer" [("safety", tagged "unsafe")]), ("source", tagged "as_cast")]), ("operand", op), ("target_type", .typeRef ty)]),
  (.binaryOp, #[("operator", .binOperator .Add .supported), ("left", op), ("right", op)]),
  (.unaryOp, #[("operator", .unOperator .Not .supported), ("operand", op)]),
  (.discriminant, #[("place", pl)]),
  (.aggregate, #[("aggregate_kind", tagged "Adt" [("def_id", defRef), ("variant_index", n 2), ("generic_args", arr [tagged "const" [("value", tc ty)]]), ("user_type_annotation", tagged "annotation_ref" [("index", n 1)]), ("active_union_field", n 4)]), ("operands", arr [op])]),
  (.copyForDeref, #[("place", pl)]),
  (.wrapUnsafeBinder, #[("operand", op), ("type", .typeRef ty)]),
  (.reborrow, #[("type", .typeRef ty), ("mutability", tagged "mutable"), ("place", pl)])]

private def statements (ty : Nat) : Array (StatementVariant × Array (String × TypedValue)) := #[
  (.assign, #[("place", pl), ("rvalue", .rvalue .repeat .supported #[("operand", op), ("count", tc ty)])]),
  (.fakeRead, #[("cause", tagged "matched_place" [("hoisted_from", defRef)]), ("place", pl)]),
  (.setDiscriminant, #[("place", pl), ("variant_index", n 2)]),
  (.storageLive, #[("local", .localRef 0)]), (.storageDead, #[("local", .localRef 0)]),
  (.placeMention, #[("place", pl)]),
  (.ascribeUserType, #[("place", pl), ("user_type_projection", .userTypeProjection ⟨.supported, some 2, some #[.deref, .field 1, .index, .constantIndex 1 3 false, .subslice 1 2 true, .downcast (some "V") 2, .opaqueCast, .unwrapUnsafeBinder, .phantomDeref], .null⟩), ("variance", tagged "contravariant")]),
  (.coverage, #[("coverage", tagged "point" [("point_kind", s "function_end"), ("hir_id", obj [("owner_def_id", defRef), ("local_id", n 3)])])]),
  (.intrinsic, #[("intrinsic", s "CopyNonOverlapping"), ("src", op), ("dst", op), ("count", op)]),
  (.constEvalCounter, #[]), (.nop, #[]),
  (.backwardIncompatibleDropHint, #[("place", pl), ("reason", tagged "edition_2024")])]

private def asm (ty : Nat) (span : SourceSpanData) : Array (String × TypedValue) := #[
  ("asm_macro", s "asm"), ("template", arr [tagged "string" [("text", s "x")], tagged "placeholder" [("operand_index", n 0), ("modifier", s "e"), ("span", .sourceSpan span)]]),
  ("operands", arr [
    tagged "in" [("register", tagged "register_class" [("arch", s "X86_64"), ("name", s "reg")]), ("value", op)],
    tagged "out" [("register", tagged "register" [("arch", s "X86_64"), ("name", s "rax")]), ("late", b true), ("place", pl)],
    tagged "inout" [("register", tagged "register_class" [("arch", s "X86_64"), ("name", s "reg")]), ("late", b false), ("input", op), ("output", nil)],
    tagged "const" [("value", constant ty span)], tagged "sym_fn" [("value", constant ty span)],
    tagged "sym_static" [("def_id", defRef)], tagged "label" [("target_index", n 0)]]),
  ("options", obj ((["pure", "nomem", "readonly", "preserves_flags", "noreturn", "nostack", "att_syntax", "raw", "may_unwind"]).map (fun key => (key, b false)))),
  ("line_spans", arr [.sourceSpan span]), ("targets", arr [.blockRef 0]), ("unwind", unwind)]

private def terms (ty : Nat) (span : SourceSpanData) : Array (TerminatorVariant × Array (String × TypedValue)) := #[
  (.goto, #[("target", .blockRef 0), ("loop_hints", arr [tagged "Hint", tagged "Full", tagged "Never", tagged "Count" [("count", n 7)]])]),
  (.switchInt, #[("discriminant", op), ("targets", arr [obj [("value", s "18446744073709551615"), ("target", .blockRef 0)]]), ("otherwise", .blockRef 0)]),
  (.unwindResume, #[]), (.unwindTerminate, #[("reason", tagged "in_cleanup")]), (.return, #[]), (.unreachable, #[]),
  (.drop, #[("place", pl), ("target", .blockRef 0), ("unwind", tagged "Terminate" [("reason", tagged "abi")]), ("replace", b true), ("async_drop", n 0)]),
  (.call, #[("function", op), ("args", arr [obj [("operand", op), ("span", .sourceSpan span)]]), ("destination", pl), ("target", .blockRef 0), ("unwind", tagged "Cleanup" [("target", .blockRef 0)]), ("call_source", tagged "normal_call"), ("function_span", .sourceSpan span)]),
  (.tailCall, #[("function", op), ("args", arr []), ("function_span", .sourceSpan span)]),
  (.assert, #[("condition", op), ("expected", b false), ("message", tagged "ResumedAfterDrop" [("coroutine_kind", tagged "desugared" [("desugaring", s "async_gen"), ("source", s "closure")])]), ("target", .blockRef 0), ("unwind", unwind)]),
  (.yield, #[("value", op), ("resume", .blockRef 0), ("resume_arg", pl), ("drop", n 0)]), (.coroutineDrop, #[]),
  (.falseEdge, #[("real_target", .blockRef 0), ("imaginary_target", .blockRef 0)]),
  (.falseUnwind, #[("real_target", .blockRef 0), ("unwind", tagged "Unreachable")]), (.inlineAsm, asm ty span)]

def main (args : List String) : IO Unit := do
  let path ← match args with | path :: _ => pure path | [] => throw (IO.userError "expected compiler fixture path")
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let some original := decoded.document.bodies[0]? | throw (IO.userError "empty bodies")
  let some first := original.blocks[0]? | throw (IO.userError "empty blocks")
  let info := first.terminator.sourceInfo
  let some decl := original.locals[0]? | throw (IO.userError "empty locals")
  let ty := decl.typeId
  let ctx := LowerContext.ofTypes decoded.document.types
  let input := { original.toBodyCore with argumentCount := 0, spreadArgument := none }
  let lower (ss : Array MirNode) (term : TypedValue) := lowerBody ctx { input with blocks := #[{ first with id := 0, statements := ss, terminator := ⟨term, info⟩ }] }
  for (kind, fs) in rvalues ty do
    let _ ← must (lower #[⟨.statement .assign .supported #[("place", pl), ("rvalue", .rvalue kind .supported fs)], info⟩] (.terminator .return .supported #[]))
  for (kind, fs) in statements ty do
    let _ ← must (lower #[⟨.statement kind .supported fs, info⟩] (.terminator .return .supported #[]))
  for (kind, fs) in terms ty info.span do
    let _ ← must (lower #[] (.terminator kind .supported fs))
  let pending ← must (lower #[⟨.statement .assign .supported #[("place", pl), ("rvalue", .rvalue .threadLocalRef .incomplete #[("def_id", defRef)])], info⟩] (.terminator .return .supported #[]))
  unless !pending.obligations.isEmpty && pending.definitions.contains ⟨2, 7⟩ && pending.definitions[0]? == input.definitionId && pending.definitions.size == 2 do
    throw (IO.userError "compiler obligations or crate-qualified definition identity were lost")
  let own ← must pending.ownDefinitionId
  unless own == 0 do throw (IO.userError "standalone body did not seed its own compiler identity")
  let missing ← must (lowerBody ctx { input with definitionId := none, blocks := #[{ first with id := 0, statements := #[], terminator := ⟨.terminator .return .supported #[], info⟩ }] })
  unless !missing.obligations.isEmpty && !missing.ownDefinitionId.isOk do
    throw (IO.userError "missing source identity became an invented frame definition")
  let mkBody (self other : DefinitionId) (name : String) : BodyCore :=
    { input with
      definitionId := some self
      defPath := name
      blocks := #[{ first with
        id := 0
        statements := #[⟨.statement .assign .supported #[("place", pl), ("rvalue", .rvalue .aggregate .supported #[("aggregate_kind", tagged "Closure" [("def_id", obj [("crate", n other.crateIndex), ("index", n other.index)]), ("generic_args", arr [tagged "const" [("value", tc ty)]])]), ("operands", arr [])])], info⟩]
        terminator := ⟨.terminator .call .supported #[
          ("function", .operand .constant .supported #[("constant", obj [
            ("type", .typeRef ty), ("span", .sourceSpan info.span), ("user_type_annotation", nil),
            ("constant", obj [("source", tagged "unevaluated" [("def_id", obj [("crate", n other.crateIndex), ("index", n other.index)]), ("generic_args", arr [tagged "const" [("value", tc ty)]]), ("promoted", nil), ("type", .typeRef ty)])])])]),
          ("args", arr []), ("destination", pl), ("target", nil), ("unwind", unwind),
          ("call_source", tagged "normal_call"), ("function_span", .sourceSpan info.span)], info⟩ }] }
  let linked ← must (lowerBodies ctx #[mkBody ⟨1, 4⟩ ⟨1, 5⟩ "a", mkBody ⟨1, 5⟩ ⟨1, 4⟩ "b"])
  unless linked.definitions == #[⟨1, 4⟩, ⟨1, 5⟩] && linked.typeConstants.size == 1 do
    throw (IO.userError "cross-body definition or generic-constant interning lost identity")
  let linkedA ← match linked.bodies[0]? with | some b => pure b | none => throw (IO.userError "missing a")
  let linkedB ← match linked.bodies[1]? with | some b => pure b | none => throw (IO.userError "missing b")
  let closureRef (body : LoweredBody) : Option (Nat × Nat) := do
    let block ← body.body.basicBlocks[0]?
    let statement ← block.statements[0]?
    match statement.kind with
    | .Assign _ (.Aggregate (.Closure defId #[.Const constId]) _) => some (defId, constId)
    | _ => none
  unless closureRef linkedA == some (1, 0) && closureRef linkedB == some (0, 0) do
    throw (IO.userError "mutually recursive references use inconsistent compiler IDs")
  let callee (body : LoweredBody) : Option Nat := do
    let block ← body.body.basicBlocks[0]?
    match block.terminator.kind with
    | .Call (.Constant c) _ _ _ _ _ _ =>
      match c.value with | .Unevaluated u _ => some u.definition | _ => none
    | _ => none
  unless callee linkedA == some 1 && callee linkedB == some 0 do
    throw (IO.userError "mutually recursive Call references lost program-global identities")
  let standaloneCore := { mkBody ⟨3, 99⟩ ⟨1, 4⟩ "never_called" with
    blocks := #[{ first with id := 0, statements := #[], terminator := ⟨.terminator .return .supported #[], info⟩ }] }
  let syntheticDoc := { decoded.document with
    bodies := #[⟨mkBody ⟨1, 4⟩ ⟨1, 5⟩ "a", #[]⟩,
      ⟨mkBody ⟨1, 5⟩ ⟨1, 4⟩ "b", #[]⟩,
      ⟨mkBody ⟨1, 4⟩ ⟨1, 5⟩ "a_same_source", #[]⟩,
      ⟨standaloneCore, #[]⟩]
    instances := #[] }
  let program ← must (lowerProgram syntheticDoc)
  let rootA ← must (program.rootDefinitionId 0)
  let rootB ← must (program.rootDefinitionId 1)
  let sameA ← must (program.rootDefinitionId 2)
  let uncalled ← must (program.rootDefinitionId 3)
  unless rootA == sameA && rootA != rootB && program.bundle.definitions[uncalled]? == some ⟨3, 99⟩ do
    throw (IO.userError "root alias or never-called root identity lost during program seeding")
  for lowered in program.bundle.bodies do
    unless lowered.definitions == program.bundle.definitions && lowered.typeConstants == program.bundle.typeConstants && lowered.spans == program.bundle.spans do
      throw (IO.userError "identity seeding rewrote shared constant/span tables inconsistently")
  let probeInstance? := decoded.document.instances.find? fun instNode =>
    match instNode.body with
    | some body => body.blocks.any fun block =>
        block.statements.any (fun node => containsProbe node.value) || containsProbe block.terminator.value
    | none => false
  let some probeInstance := probeInstance? | throw (IO.userError "fixture has no exact vtable probe to mutate")
  let some probeBody := probeInstance.body | throw (IO.userError "probe instance body disappeared")
  let mutatedCore := { probeBody.toBodyCore with blocks := probeBody.blocks.map fun block =>
    { block with
      statements := block.statements.map fun node => { node with value := mutateProbeStatus node.value }
      terminator := { block.terminator with value := mutateProbeStatus block.terminator.value } } }
  let mutatedLowering ← must (lowerBody (LowerContext.ofDocument decoded.document) mutatedCore)
  unless mutatedLowering.obligations.any (fun obligation =>
      obligation.message == "compiler metadata status remains unsupported") do
    throw (IO.userError "mutated typed MIR inherited a raw-document vtable-probe exemption")
  IO.println "all 13 rvalue, 12 statement, 15 terminator source constructor branches lowered; typed metadata and execution obligations retained"
