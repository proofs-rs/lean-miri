import Miri.Input.CtfeMirSourceCodec
open Lean Miri.Input Miri.Interpreter.CompileTime
open CallFrame SourceStack
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
private def constant (n : Nat) : Reference := .direct n none
private def leaf : SourceStack.Source := {
  definition := 90001,name := "outside-prefix",required := #[constant 11,constant 11]
  cleanup := #[false],program := {locals := #[.uint 32],argumentCount := 0,blocks := #[{
    statements := #[.assign ⟨0,#[]⟩ (.use (.sourceValue ⟨.literalValue,0,none,.uint 32 7⟩) true)]
    terminator := .ret}]}}
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "wire source path")
  let json ← must (Json.parse (← IO.FS.readFile path))
  let raw ← must (json.getObjValAs? (Array Json) "sources")
  let sources ← must (raw.mapM CtfeMirSourceCodec.read)
  let wireSources := sources
  let programs ← must (sources.mapM CtfeMirSource.stackSource)
  check (!(SourceStack.lookup #[] leaf.definition).isOk) "missing source accepted"
  check (!(SourceStack.lookup #[leaf,leaf] leaf.definition).isOk) "duplicate source accepted"
  let resolve (_ : Array Nat) (_ : Reference) : Except String Value := .ok (.uint 32 0)
  let (entered,machine) := SourceStack.push #[leaf] resolve leaf.definition #[] #[] none {}
  must entered
  check (machine.requiredRequests.size == 2) "duplicate required occurrence lost"
  match SourceStack.run #[leaf] ⟨64,false,true⟩ resolve 10 machine with
  | .returned (.uint 32 7) _ => pure ()
  | _ => throw (IO.userError "physical source outside dense prefix failed")
  let request (_ : Frame) (_ : Reference) (world : Nat) : Except String Unit × Nat :=
    (if world == 1 then .error "second request" else .ok (),world+1)
  let (result,machine,world) := SourceStack.pushWithWorld #[leaf] request leaf.definition #[] #[] none {} 0
  check (!result.isOk && world == 2 && machine.requiredRequests.size == 2 &&
    machine.frames.head?.any (·.current.isNone) && machine.trace.isEmpty) "entry error discarded World/initialized PC"
  let body : CallFrame.Program := {locals := #[.uint 32],argumentCount := 0,blocks := #[{
    statements := #[.assign ⟨0,#[]⟩ (.binary .addWithOverflow (.constant (constant 1)) (.constant (constant 2)))]
    terminator := .ret}]}
  let initial ← must (CallFrame.initializeState body #[])
  let requestBody (reference : Reference) : EStateM String (List Nat) Value := fun world =>
    let key := match reference with | .direct key _ _ _ | .associated key _ _ _ _ | .parameterConstant key _ _ _ => key
    .error "first operand" (world ++ [key])
  let (result,world) := CallFrame.stepWithWorld body ⟨64,false,true⟩ requestBody initial []
  check (world == [1]) "failed left operand evaluated right operand or discarded World"
  match result with
  | .failed "first operand" state => check (state.steps == 0 && state.block == 0 && state.statement == 0) "failure moved PC"
  | _ => throw (IO.userError "failed operand did not stop")
  let some root := raw.find? (fun value => (value.getObjValAs? String "policy").toOption == some "scalar_u32_calls_v1")
    | throw (IO.userError "calls policy source absent")
  check (!(CtfeMirSourceCodec.read (root.setObjVal! "policy" (toJson "scalar_u32"))).isOk) "new payload admitted under old scalar policy"
  check (!(CtfeMirSourceCodec.read (root.setObjVal! "user_type_annotations" (toJson #["fabricated"]))).isOk) "nonempty PostCleanup annotation table accepted"
  let some scalar := raw.find? (fun value => (value.getObjValAs? String "policy").toOption == some "scalar_u32")
    | throw (IO.userError "old scalar source absent")
  check (!(CtfeMirSourceCodec.read (scalar.setObjVal! "user_type_annotations" (toJson (#[] : Array Json)))).isOk) "old schema expanded"
  for source in programs do must (SourceStack.validateSource source)
  let bad := {leaf with program := {leaf.program with locals := #[.uint 64]}}
  check (!(SourceStack.validateSource bad).isOk) "unsupported scalar type accepted"
  let bad := {leaf with cleanup := #[true]}
  check (!(SourceStack.validateSource bad).isOk) "cleanup entry accepted"
  let some calls := programs.find? (fun source => source.program.blocks.any (fun block => block.terminator matches .call _))
    | throw (IO.userError "call source absent")
  let some block := calls.program.blocks[0]? | throw (IO.userError "call block absent")
  let .call call := block.terminator | throw (IO.userError "call terminator absent")
  let malformed (call : Call) : SourceStack.Source :=
    {calls with program := {calls.program with blocks := calls.program.blocks.set! 0 {block with terminator := .call call}}}
  must (SourceStack.validateSource (malformed {call with functionUserType := some 123}))
  let spanCount ← must (json.getObjValAs? Nat "span_count")
  let some outer := wireSources.find? (fun source => source.definition.index == calls.definition)
    | throw (IO.userError "outer call source absent")
  let outsideSpan := {outer with program := .calls (malformed {call with functionOperandSpan := spanCount})}
  check (!(CtfeMirSource.validateReferences spanCount (fun _ => true) outsideSpan).isOk) "FnDef operand span bounds omitted"
  check (!(SourceStack.validateSource (malformed {call with argumentSpans := #[]})).isOk) "call span domain omitted"
  check (!(SourceStack.validateSource (malformed {call with unwind := .cleanup 0})).isOk) "forged cleanup unwind accepted"
  check (!(SourceStack.validateSource (malformed {call with functionSourceClass := .typeValue})).isOk) "forged FnDef source class accepted"
  check (!(SourceStack.validateSource (malformed {call with abi := "C"})).isOk) "unsupported call ABI accepted"
  check (!(SourceStack.validateSource (malformed {call with typeArguments := #[1]})).isOk) "generic call accepted"
  check (!(SourceStack.validateSource (malformed {call with trackCaller := true})).isOk) "track_caller accepted"
  check (!(SourceStack.validateSource (malformed {call with destination := ⟨99999,#[]⟩})).isOk) "missing call destination accepted"
  let forged := malformed {call with callee := 999999}
  let sources := programs.map (fun source => if source.definition == calls.definition then forged else source)
  let (entered,machine) := SourceStack.push sources resolve forged.definition #[] #[] none {}
  must entered
  match SourceStack.run sources ⟨64,false,true⟩ resolve 100 machine with
  | .failed "missing or forged source definition" _ => pure ()
  | _ => throw (IO.userError "display-name-preserving forged callee accepted")
  let cleanup := {leaf with
    cleanup := #[false,true]
    program := {leaf.program with blocks := leaf.program.blocks.push {statements := #[],terminator := .resume}}}
  must (SourceStack.validateSource cleanup)
  let state ← must (initializeState cleanup.program #[])
  let machine : Machine := {frames := [{source := cleanup,current := some {state with block := 1}}]}
  match SourceStack.run #[cleanup] ⟨64,false,true⟩ resolve 1 machine with
  | .failed "unsupported CTFE cleanup block entered" machine => check (machine.steps == 0) "cleanup succeeded"
  | _ => throw (IO.userError "forced cleanup entry did not reject")
  let some template := wireSources[0]? | throw (IO.userError "source metadata absent")
  let outerRoot : CtfeMirSource.LintRoot := ⟨⟨0,777⟩,1⟩
  let innerRoot : CtfeMirSource.LintRoot := ⟨⟨0,888⟩,2⟩
  let withRoot (root : CtfeMirSource.LintRoot) : CtfeMirSource.Source := {template with
    statementSources := #[#[]],terminatorSources := #[⟨⟨0⟩,0⟩]
    scopes := #[⟨⟨0⟩,none,some root⟩]}
  check ((CtfeMirSource.bestLintRoot [(withRoot innerRoot,0,0),(withRoot outerRoot,0,0)]).toOption == some (some outerRoot))
    "lint scope selected innermost instead of root-first source"
  IO.println "PASS source-wire policies, physical keys, duplicate/pending order, EState World/operand order, scalar and cleanup controls"
