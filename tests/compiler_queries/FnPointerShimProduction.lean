import Miri.Input.Decoder
import Miri.Input.CallResolution

/-! Fresh source-only FnPtr shim demands. The independent rustc body oracle
is compared after explicitly rebasing its two lang-item physical identities
into this export's crate namespace. No expected MIR is synthesized by Python. -/
open Lean Miri.Input Miri.Input.GenericSubstitution

private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def ensure (condition : Bool) (message : String) : Except String Unit :=
  unless condition do throw message
private def replaceField (object : Json) (key : String) (value : Json) : Except String Json := do
  let fields := (← object.getObj?).toArray.filter (·.1 != key)
  pure (Json.mkObj ((fields.push (key,value)).toList))
private def remap (mapping : Array (DefinitionIdentity × DefinitionIdentity)) : Nat → GenericSubstitution.Term → Except String GenericSubstitution.Term
  | 0,_ => throw "oracle identity rebasing exhausted"
  | fuel + 1,term => do
    match term with
    | .definition sort tag identity children =>
      let identity := ((mapping.find? (·.1 == identity)).map (·.2)).getD identity
      pure (.definition sort tag identity (← children.mapM (remap mapping fuel)))
    | .node sort tag payload children =>
      let payload ← if sort == .aggregate && tag == "signature" then
        (·.compress) <$> Json.parse payload else pure payload
      pure (.node sort tag payload (← children.mapM (remap mapping fuel)))
    | .binder variables child => pure (.binder variables (← remap mapping fuel child))
    | _ => pure term

private def compareBody (world : RuntimeArrayTypes.World) (reference : FnPointerShimRef)
    (direction : String) (selfType : Nat) (actual : Miri.MIR.Body) (oracle : Array Json) : Except String Unit := do
  let selfTerm ← GenericInstantiationWorld.ofType world.arena 16384 selfType >>= remap #[] 16384
  let row ← match ← oracle.findM? (fun row => do
      let kind ← (← row.getObjVal? "kind").getStr?
      let term ← GenericMaterialCodec.readTerm 16384 (← row.getObjVal? "self_type") >>= remap #[] 16384
      pure (kind == direction && term == selfTerm)) with
    | some row => pure row | none => throw s!"fresh shim Self has no independent rustc oracle row: {direction}, type {selfType}, term {repr selfTerm}"
  let nonNull ← GenericMaterialCodec.readTerm 16384 (← row.getObjVal? "non_null_type")
  let .definition .type "adt" oldNonNull (.cons (.definition .type "foreign" oldCode .nil) .nil) := nonNull
    | throw "oracle NonNull<Code> identity shape changed"
  let mapping := #[(oldNonNull,← world.arena.identity reference.nonNullDefinition),
                   (oldCode,← world.arena.identity reference.codeDefinition)]
  let read (json : Json) := GenericMaterialCodec.readTerm 16384 json >>= remap mapping 16384
  let expected ← row.getObjVal? "expected"
  let expectedTypes ← (← (← expected.getObjVal? "locals").getArr?).mapM read
  let actualTypes ← actual.locals.mapM (fun id => GenericInstantiationWorld.ofType world.arena 16384 id >>= remap #[] 16384)
  ensure (actualTypes == expectedTypes) "production shim locals differ from rebased independent rustc body"
  let resolve (term : GenericSubstitution.Term) : Except String Nat := do
    let some index := expectedTypes.findIdx? (· == term) | throw "oracle cast target is not a local type"
    let some id := actual.locals[index]? | throw "production local type disappeared"
    pure id
  let info : Miri.MIR.SourceInfo := ⟨⟨reference.sourceSpan.spanId⟩,0⟩
  let blocks ← (← (← expected.getObjVal? "blocks").getArr?).mapM fun block => do
    let statements ← (← (← block.getObjVal? "statements").getArr?).mapM fun statement => do
      let cast ← match ← (← statement.getObjVal? "cast").getStr? with
        | "transmute" => pure Miri.MIR.CastKind.Transmute | "fn_ptr_to_ptr" => pure .FnPtrToPtr
        | _ => throw "unknown oracle cast"
      let destination ← (← statement.getObjVal? "destination").getNat?
      let operand ← (← statement.getObjVal? "operand").getNat?
      let target ← resolve (← read (← statement.getObjVal? "target"))
      pure (⟨info,.Assign ⟨destination,#[]⟩ (.Cast cast (.Move ⟨operand,#[]⟩) target)⟩ : Miri.MIR.Statement)
    ensure ((← (← block.getObjVal? "terminator").getStr?) == "return") "unknown oracle terminator"
    pure (⟨statements,⟨info,.Return⟩,← (← block.getObjVal? "cleanup").getBool?⟩ : Miri.MIR.BasicBlock)
  let spread ← expected.getObjVal? "spread_argument"
  ensure ((← (← expected.getObjVal? "phase").getStr?) == "runtime_optimized" && spread == .null)
    "oracle phase or spread changed"
  ensure (actual.phase == .Runtime .Optimized && actual.argumentCount == (← (← expected.getObjVal? "argument_count").getNat?) &&
    actual.spreadArgument.isNone && actual.basicBlocks == blocks) "production shim differs from complete independent rustc body"

def main (args : List String) : IO Unit := do
  let (path,oraclePath,expectedCount,novelOraclePath) ← match args with
    | [path,oraclePath] => pure (path,oraclePath,2,none)
    | [path,oraclePath,count] => match count.toNat? with
      | some count => pure (path,oraclePath,count,none)
      | none => throw (IO.userError "expected a numeric shim count")
    | [path,oraclePath,count,novelOracle] => match count.toNat? with
      | some count => pure (path,oraclePath,count,some novelOracle)
      | none => throw (IO.userError "expected a numeric shim count")
    | _ => throw (IO.userError "expected fresh shim export, independent rustc oracle and optional count")
  let text ← IO.FS.readFile path
  let raw ← must (Json.parse text)
  let document := (← must (decodeJson text)).document
  let oracle ← must (Json.parse (← IO.FS.readFile oraclePath) >>= Json.getArr?)
  let novelOracle ← match novelOraclePath with
    | none => pure none
    | some path => some <$> must (Json.parse (← IO.FS.readFile path) >>= Json.getArr?)
  let metadata ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let initial ← must ((RuntimeArrayTypes.create metadata).mapError reprStr)
  let prepared ← must (CallResolution.prepareWithRuntime metadata (← must (lowerProgram document)))
  let mut count := 0
  for (seed,index) in document.bodies.zipIdx do
    let .fnPointerShim reference := seed | continue
    let (loaded,world) ← must ((CallResolution.loadedBodyOfInstance prepared reference.instanceId).run initial)
    unless loaded.identity.index == index do throw (IO.userError "material shim source lost its exact body identity")
    let (kind,selfType,direction) ← must do
      let some source := document.instances[reference.instanceId]? | throw "shim instance disappeared"
      match source.instanceKind with
      | .Shim (.FnPtrAsPtr definition selfType) => pure (definition,selfType,"as_pointer")
      | .Shim (.FnPtrFromPtr definition selfType) => pure (definition,selfType,"from_pointer")
      | _ => throw "unexpected shim source kind"
    must (compareBody world reference direction selfType loaded.body oracle)
    let (again,repeated) ← must ((CallResolution.loadedBodyOfInstance prepared reference.instanceId).run world)
    unless again.identity == loaded.identity && again.body == loaded.body &&
        repeated.arena.constructedTypes == world.arena.constructedTypes && repeated.bodies == world.bodies do
      throw (IO.userError "repeated shim body demand duplicated constructor identities")
    let novel : RuntimeArrayTypes.CompilerM (Nat × Nat × Miri.Interpreter.LoadedBody) := do
      let world ← get
      let some source := document.types[selfType]? | throw "original FnPtr source is absent"
      let constructor ← match world.arena.materialKey source with
        | .ok value => pure value | .error error => throw error
      let some (.functionPointer signature) := constructor
        | throw "original FnPtr signature lacks raw constructor"
      let ty ← RuntimeArrayTypes.liftType (TypeArena.World.internType (.functionPointer {signature with safe := !signature.safe}))
      unless ty >= document.types.size do throw "novel shim test unexpectedly reused a source FnPtr type"
      let shim := if direction == "as_pointer" then Miri.Interpreter.CallShimKind.FnPtrAsPtr kind ty else .FnPtrFromPtr kind ty
      let instanceId ← RuntimeArrayTypes.internInstance (.Shim shim) #[.Type ty]
      unless instanceId >= document.instances.size do throw "novel shim instance did not append outside material prefix"
      pure (instanceId,ty,← CallResolution.loadedBodyOfInstance prepared instanceId)
    let ((instanceId,novelType,novelBody),novelWorld) ← must (novel.run world)
    if let some oracle := novelOracle then
      must (compareBody novelWorld reference direction novelType novelBody.body oracle)
    unless novelBody.identity.index >= document.bodies.size do throw (IO.userError "novel shim body did not append outside material prefix")
    let (body,_) ← must ((prepared.program.resolveBodyIdentity novelBody.identity).run novelWorld)
    unless body.input.instanceId == instanceId && body.body == novelBody.body do
      throw (IO.userError "constructed shim body lost current instance ownership")
    let bodies ← must ((← must (raw.getObjVal? "bodies")).getArr?)
    let some body := bodies[index]? | throw (IO.userError "raw shim seed disappeared")
    for (key,value) in [("locals",Json.arr #[]),("code_definition",toJson document.definitions.size)] do
      let malformed ← must (replaceField body key value)
      let malformed ← must (replaceField raw "bodies" (.arr (bodies.set! index malformed)))
      if (decodeJson malformed.compress).isOk then throw (IO.userError s!"raw shim accepted invalid field {key}")
    let types ← must ((← must (raw.getObjVal? "types")).getArr?)
    let some selfNode := types[selfType]? | throw (IO.userError "raw FnPtr Self disappeared")
    let selfShape ← must (selfNode.getObjVal? "shape")
    for boundVariable in [Json.mkObj [("kind",toJson "const")],
        Json.mkObj [("kind",toJson "type"),("type_kind",Json.mkObj [("kind",toJson "anonymous")])]] do
      let shape ← must (replaceField selfShape "signature_bound_variables" (.arr #[boundVariable]))
      let malformedNode ← must (replaceField selfNode "shape" shape)
      let malformed ← must (replaceField raw "types" (.arr (types.set! selfType malformedNode)))
      if (decodeJson malformed.compress).isOk then throw (IO.userError "raw shim accepted a non-region Self binder")
    count := count + 1
  unless count == expectedCount do throw (IO.userError s!"expected {expectedCount} raw FnPtr conversion shims, found {count}")
  IO.println s!"PASS {count} production FnPtr source shims match independent rustc bodies; novel type/instance/body identities and malformed-source controls pass"
