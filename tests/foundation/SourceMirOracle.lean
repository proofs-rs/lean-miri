import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceCompilerBodies
import Miri.Input.Decoder
open Lean Miri Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def sameType (a b : Input.SourceTypes.Concrete) : Bool := go 1024 a b
where
  go (fuel : Nat) (a b : Input.SourceTypes.Concrete) : Bool :=
    match fuel,a,b with
    | 0,_,_ => false
    | _+1,.primitive k v,.primitive k' v' => k == k' && v == v'
    | n+1,.pointer k t,.pointer k' t' => k == k' && go n t t'
    | n+1,.array t l,.array t' l' => l == l' && go n t t'
    | n+1,.tuple ts,.tuple ts' => ts.size == ts'.size && (ts.zip ts').all (fun (a,b) => go n a b)
    | n+1,.functionPointer inputs out safety abi variadic,.functionPointer inputs' out' safety' abi' variadic' =>
      inputs.size == inputs'.size && (inputs.zip inputs').all (fun (a,b) => go n a b) &&
        go n out out' && safety == safety' && abi == abi' && variadic == variadic'
    | _,_,_ => false
private def sameTypes (a b : Array Input.SourceTypes.Concrete) : Bool :=
  a.size == b.size && (a.zip b).all (fun (a,b) => sameType a b)
private def typesOf (world : Input.SourceCompilerWorld.World) (body : MIR.Body) : Except String (Array Input.SourceTypes.Concrete) :=
  body.locals.mapM (Input.SourceConcreteTypes.concreteType world 64)
private def spanPayload (world : Input.SourceCompilerWorld.World) (id : Nat) :
    Except String (Input.SourceSpanData × String) := do
  let some data := world.canonical.spans[id]? | throw "oracle span absent"
  let some file := world.canonical.files[data.file]? | throw "oracle span filename absent"
  return ({data with file := 0},file)
/-- Test-only rebinding of independent compilation-local type and span handles.
This compares complete MIR constructors in the exercised common domain; it
makes no claim of cross-session rustc span or type identity. -/
private def normalized (world : Input.SourceCompilerWorld.World)
    (keys : Array Input.SourceTypes.Concrete) (body : MIR.Body) : Except String MIR.Body := do
  let typeId := fun id => do
    let key ← Input.SourceConcreteTypes.concreteType world 64 id
    let some index := keys.findIdx? (fun value => sameType value key) | throw "oracle constant type not among local shapes"
    pure index
  let op := fun operand => do
    match operand with
    | .Constant c =>
      match c.value with
      | .Val value ty => pure (MIR.Operand.Constant {c with span := ⟨0⟩,value := .Val value (← typeId ty)})
      | .SourceRequest .. => throw "oracle comparison requires the actual evaluated constant witness"
    | .Copy p => pure (.Copy p)
    | .Move p => pure (.Move p)
    | _ => throw "oracle operand outside exercised domain"
  let blocks ← body.basicBlocks.mapM fun block => do
    let statements ← block.statements.mapM fun statement => do
      let kind ← match statement.kind with
        | .Assign place (.Use value retag) => pure (MIR.StatementKind.Assign place (.Use (← op value) retag))
        | .StorageLive id => pure (.StorageLive id)
        | .StorageDead id => pure (.StorageDead id)
        | .Nop => pure .Nop
        | _ => throw "oracle statement outside exercised domain"
      pure {statement with sourceInfo := {statement.sourceInfo with span := ⟨0⟩},kind}
    unless block.terminator.kind == .Return do throw "oracle terminator outside exercised domain"
    pure {block with statements,terminator := {block.terminator with sourceInfo := {block.terminator.sourceInfo with span := ⟨0⟩}}}
  return {body with locals := ← body.locals.mapM typeId,basicBlocks := blocks}

def main (paths : List String) : IO Unit := do
  let [sourcePath,referencePath] := paths | throw (IO.userError "expected finite source and independent schema12 oracle")
  let source ← checked (decode (← checked (Json.parse (← IO.FS.readFile sourcePath))))
  let mut world ← checked (compilerEntrySeed source)
  let reference := (← checked (Input.decodeJson (← IO.FS.readFile referencePath))).document
  let referenceWorld : Input.SourceCompilerWorld.World := {canonical := reference}
  let initialNodes := world.canonical.instances
  for node in initialNodes do
    let key ← checked (Input.SourceCompilerWorld.keyOf world node.id)
    let (updated,_) ← checked (Input.SourceCompilerBodies.demandLoadedBody world node.id)
    world := updated
    let id ← checked (Input.SourceCompilerWorld.bodyId world node.id)
    let some actual := world.canonical.bodies[id]? | throw (IO.userError "demanded source body absent")
    let matching := reference.bodies.filter fun b =>
      b.definitionId.bind (reference.definitions[·]?) == some key.definition
    let [expected] := matching.toList | throw (IO.userError "schema12 exact raw owner body absent/ambiguous")
    let some expectedInstance := reference.instances[expected.instanceId]? | throw (IO.userError "oracle instance absent")
    unless expectedInstance.genericArgs.size == key.arguments.size do throw (IO.userError "oracle full generic argument count differs")
    for (a,b) in key.arguments.zip expectedInstance.genericArgs do
      match a,b with
      | .Type a,.Type b =>
        unless sameType (← checked (Input.SourceConcreteTypes.concreteType world 64 a))
            (← checked (Input.SourceConcreteTypes.concreteType referenceWorld 64 b)) do
          throw (IO.userError "oracle concrete substitution differs")
      | _,_ => throw (IO.userError "oracle generic argument outside exercised domain")
    let actualTypes ← checked (typesOf world actual.mir)
    unless sameTypes actualTypes (← checked (typesOf referenceWorld expected.mir)) do throw (IO.userError "oracle complete local types differ")
    unless (← checked (normalized world actualTypes actual.mir)) ==
        (← checked (normalized referenceWorld actualTypes expected.mir)) do throw (IO.userError "oracle complete MIR constructors differ")
    unless actual.localSources.size == expected.localSources.size &&
        actual.sourceScopes.size == expected.sourceScopes.size && actual.requiredConsts.size == expected.requiredConsts.size do
      throw (IO.userError "oracle source metadata/required-constant arity differs")
    unless (← checked (spanPayload world actual.spanId)) ==
        (← checked (spanPayload referenceWorld expected.spanId)) &&
        (← checked (spanPayload world actual.preambleDefSpanId)) ==
        (← checked (spanPayload referenceWorld expected.preambleDefSpanId)) do
      throw (IO.userError "oracle body/definition source coordinates differ")
    for (a,b) in actual.localSources.zip expected.localSources do
      unless a.scope == b.scope && (← checked (spanPayload world a.spanId)) ==
          (← checked (spanPayload referenceWorld b.spanId)) do
        throw (IO.userError "oracle local source info differs")
    for (a,b) in actual.sourceScopes.zip expected.sourceScopes do
      unless a.id == b.id && a.parent == b.parent && a.inlined == b.inlined && a.inlinedParent == b.inlinedParent &&
          (← checked (spanPayload world a.spanId)) == (← checked (spanPayload referenceWorld b.spanId)) do
        throw (IO.userError "oracle source scope data differs")
  IO.println "source-demand main/start full MIR constructors and substitutions match independent compiler oracle after explicit local handle rebinding"
