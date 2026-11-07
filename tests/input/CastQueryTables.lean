import Miri.Input.Reader.CastQueries

open Lean Miri.Input Miri.Input.Reader Miri.Interpreter

private instance : Inhabited CastQueryData :=
  ⟨⟨0,.error "missing row",.error "missing row",.error "missing row",.error "missing row",
    .error "missing row",.error "missing row",.error "missing row"⟩⟩

private def must (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def reference (id : Nat) : Json := Json.mkObj [("$lean_miri_shared_ref",toJson id)]
private def ty (id : Nat) : Json := Json.mkObj [("type_id",toJson id)]
private def row (kind : String) (value : Json) : Json := Json.mkObj [
  ("query_kind",toJson kind),("typing_env",toJson "fully_monomorphized"),
  ("status",toJson "supported"),("input_type",ty 0),("args_no_bound_vars",toJson true),
  ("value",value)]
private def withField (input : Json) (key : String) (value : Json) : Except String Json := do
  let .obj fields := input | throw "expected cast fixture object"
  return Json.mkObj ((key,value) :: fields.toList.filter (·.1 != key))

private def read (nodes rows : Array Json) (instances : Array (Except String CallInstance))
    (typeCount : Nat := 1) := do
  let catalog ← must (Catalog.parse (Json.mkObj [
    ("shared_payloads",Json.mkObj [("schema_version",toJson (2 : Nat)),("nodes",.arr nodes)]),
    ("compiler_cast_queries",.arr rows)]))
  must ((CastQueryReader.read catalog typeCount instances).run (MIRReader.initial catalog.nodes.size {}))

def main : IO Unit := do
  let kind := Json.mkObj [("kind",toJson "item"),
    ("def_id",Json.mkObj [("crate",toJson (3 : Nat)),("index",toJson (4 : Nat))])]
  let instanceData := Json.mkObj [("instance_id",toJson (0 : Nat)),
    ("instance_kind",reference 0),("generic_args",.arr #[])]
  let resolved := row "resolve_fn_ptr" (reference 1)
  let (rows,state) ← read #[kind,instanceData,resolved] #[reference 2,resolved]
    #[.ok ⟨.Item 0,#[]⟩]
  unless rows.size == 2 && rows[0]!.value == .ok (.resolved (some 0)) &&
      rows[0]!.identity == rows[1]!.identity && state.compiler.definitions == #[⟨3,4⟩] do
    throw (IO.userError "cast instance identity or equivalent duplicate changed")
  let (rows,state) ← read #[kind,instanceData] #[row "resolve_fn_ptr" (reference 1)]
    #[.ok ⟨.Item 1,#[]⟩]
  unless rows[0]!.value.toOption.isNone && state.compiler.definitions.isEmpty do
    throw (IO.userError "inconsistent instance metadata accepted or failed decode leaked identities")
  let unavailable := Json.mkObj [("query_kind",toJson "resolve_fn_ptr"),
    ("typing_env",toJson "fully_monomorphized"),("status",toJson "unsupported"),
    ("input_type",ty 0),("args_no_bound_vars",toJson false)]
  let (rows,_) ← read #[] #[unavailable,unavailable,row "resolve_fn_ptr" .null,
      row "box_type" (ty 1)] #[]
  unless rows[0]!.identity == rows[1]!.identity && rows[0]!.value.toOption.isNone &&
      rows[0]!.noBoundVars == .ok false && rows[2]!.value == .ok (.resolved none) &&
      rows[3]!.value.toOption.isNone do
    throw (IO.userError "cast local unavailable/null/out-of-range evidence changed")
  let changed := Json.mkObj [("query_kind",toJson "resolve_fn_ptr"),
    ("typing_env",toJson "fully_monomorphized"),("status",toJson "unsupported"),
    ("input_type",ty 0),("args_no_bound_vars",toJson true)]
  let (rows,_) ← read #[] #[unavailable,changed] #[]
  unless rows[0]!.identity != rows[1]!.identity do
    throw (IO.userError "conflicting cast evidence collapsed")
  let pair := fun (kind : String) (value : Json) => Json.mkObj [("query_kind",toJson kind),
    ("typing_env",toJson "fully_monomorphized"),("status",toJson "supported"),
    ("input_source",ty 0),("input_target",ty 0),("value",value)]
  let (rows,_) ← read #[] #[pair "lockstep_tails"
      (Json.mkObj [("source_tail",ty 0),("target_tail",ty 0)]),
      pair "supertrait_slot" .null,pair "supertrait_slot" (toJson (7 : Nat)),
      row "box_type" (ty 0)] #[]
  unless rows[0]!.value == .ok (.tails 0 0) &&
      rows[1]!.value == .ok (.supertraitSlot none) &&
      rows[2]!.value == .ok (.supertraitSlot (some 7)) &&
      rows[3]!.value == .ok (.boxType 0) do
    throw (IO.userError "typed cast tail/slot/box evidence changed")

  -- Display/debug payloads do not participate in compiler query semantics.
  -- The two debug DAGs share their children exponentially; no comparison of
  -- expanded JSON is needed to identify the consumed typed rows.
  let mut nodes := #[Json.mkObj [("leaf",toJson true)],Json.mkObj [("leaf",toJson true)]]
  for _ in [:24] do
    let left := nodes.size - 2
    let right := nodes.size - 1
    nodes := nodes.push (Json.mkObj [("left",reference left),("right",reference left)])
    nodes := nodes.push (Json.mkObj [("left",reference right),("right",reference right)])
  let debugLeft ← must (withField (row "box_type" (ty 0)) "debug" (reference (nodes.size - 2)))
  let debugRight ← must (withField (row "box_type" (ty 0)) "debug" (reference (nodes.size - 1)))
  let debugOther ← must (withField (row "box_type" (ty 0)) "producer_display" (toJson "different debug metadata"))
  let (rows,_) ← read nodes #[debugLeft,debugRight,debugOther] #[]
  unless rows.size == 3 && rows.all (fun entry => entry.identity == rows[0]!.identity && entry.value == .ok (.boxType 0)) do
    throw (IO.userError "debug-only cast metadata changed semantic identity")
  let changedInput ← must (withField (row "box_type" (ty 0)) "input_type" (ty 1))
  let changedEnvironment ← must (withField (row "box_type" (ty 0)) "typing_env" (toJson "post_analysis"))
  let (rows,_) ← read #[] #[row "box_type" (ty 0),row "box_type" (ty 1),
      changedInput,changedEnvironment] #[] 2
  unless rows[0]!.identity != rows[1]!.identity && rows[0]!.value == .ok (.boxType 0) &&
      rows[1]!.value == .ok (.boxType 1) && rows[0]!.identity != rows[2]!.identity &&
      rows[2]!.inputType == .ok 1 && rows[0]!.identity != rows[3]!.identity &&
      rows[3]!.environment.toOption.isNone && rows[3]!.value.toOption.isNone do
    throw (IO.userError "typed cast value/input/environment conflict collapsed")
  let basePair := pair "supertrait_slot" (toJson (7 : Nat))
  let changedSource ← must (withField basePair "input_source" (ty 1))
  let changedTarget ← must (withField basePair "input_target" (ty 1))
  let malformedUnusedFlag ← must (withField basePair "args_no_bound_vars" (toJson "not a boolean"))
  let (rows,_) ← read #[] #[basePair,basePair,changedSource,changedTarget,malformedUnusedFlag] #[] 2
  unless rows[0]!.identity == rows[1]!.identity && rows[0]!.identity != rows[2]!.identity &&
      rows[0]!.identity != rows[3]!.identity && rows[0]!.identity == rows[4]!.identity &&
      rows.all (fun entry => entry.value == .ok (.supertraitSlot (some 7))) do
    throw (IO.userError "cast pair keys or unused missing/error flag semantics changed")
  let reasonA ← must (withField unavailable "reason" (toJson "reason A"))
  let reasonB ← must (withField unavailable "reason" (toJson "reason B"))
  let (rows,_) ← read #[] #[reasonA,reasonA,reasonB] #[]
  unless rows[0]!.identity == rows[1]!.identity && rows[0]!.identity != rows[2]!.identity &&
      rows.all (fun entry => entry.value.toOption.isNone) do
    throw (IO.userError "unavailable cast reasons lost their typed failure identity")
  IO.println "typed cast query semantic identity PASS"
