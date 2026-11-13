import Miri.Input.Decoder
import Miri.Input.SourceFnTraits
import Miri.Input.AliasRuntime
import Miri.Input.GenericInstantiationWorld
open Lean Miri.Input GenericSubstitution
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error e => throw (IO.userError e)
def main (args : List String) : IO Unit := do
  let [nestedSource,nestedOracle,asyncSource,asyncOracle] := args
    | throw (IO.userError "expected nested FnPtr and coroutine closure source/oracle inputs")
  let document := (← must (decodeJson (← IO.FS.readFile nestedSource))).document
  let context ← must (AliasRuntime.Context.ofDocument document)
  let oracle ← must (Json.parse (← IO.FS.readFile nestedOracle))
  let rows ← must ((← must (oracle.getObjVal? "queries")).getArr?)
  let #[row] := rows | throw (IO.userError "nested FnPtr oracle corpus changed")
  let self ← must (GenericMaterialCodec.readTerm 4096 (← must (row.getObjVal? "self")))
  let rawTuple ← must (GenericMaterialCodec.readTerm 4096 (← must (row.getObjVal? "args_tuple")))
  let wrongTuple ← must (GenericMaterialCodec.readTerm 4096 (← must (row.getObjVal? "wrong_args_tuple")))
  unless (← must ((← must (row.getObjVal? "wrong_args_proven")).getBool?))==false do
    throw (IO.userError "nested unsafe argument control unexpectedly proved in rustc")
  let empty ← must (TypeArena.World.ofMaterial #[] #[] document.definitions #[] context.generic.pointerBytes)
  let (tupleId,arena) ← must ((GenericInstantiationWorld.resolveType 4096 rawTuple).run empty)
  let worldTuple ← must (GenericInstantiationWorld.ofType arena 4096 tupleId)
  unless rawTuple != worldTuple do throw (IO.userError "nested FnPtr control did not exercise distinct header JSON ordering")
  let source : SourceFnTraits.Source := ⟨document.definitions,document.traitProgram,
    fun _ => throw "unexpected FnDef feature query in FnPtr control"⟩
  let normalize := AliasRuntime.normalizeTerm context 100000 4096 #[] #[]
  let goals ← must ((← must (row.getObjVal? "goals")).getArr?)
  let mut count := 0
  for goal in goals do
    unless ← must ((← must (goal.getObjVal? "proven")).getBool?) do
      throw (IO.userError "nested FnPtr expected real rustc positive")
    let identity ← must (GenericMaterialCodec.readDefinition (← must (goal.getObjVal? "definition")))
    let #[declaration] := document.traitProgram.traits.filter (·.definition==identity)
      | throw (IO.userError "Fn trait raw declaration absent")
    let some selected ← must (SourceFnTraits.query source normalize 4096 declaration #[self,worldTuple])
      | throw (IO.userError "Fn builtin treated header JSON ordering as different types")
    let expected ← must (GenericMaterialCodec.readTerm 4096 (← must (goal.getObjVal? "output")))
    unless selected.output==expected do throw (IO.userError "nested FnPtr Output differs from rustc")
    match ← must (AliasRuntime.solveGoal context 4096 100000 ⟨.positive,⟨identity,#[self,worldTuple]⟩⟩) with
    | .proven (.builtin ..) => pure ()
    | _ => throw (IO.userError "nested FnPtr source trait engine lacks real builtin proof")
    unless (← must (SourceFnTraits.query source normalize 4096 declaration #[self,wrongTuple])).isNone do
      throw (IO.userError "signature JSON canonicalization dropped nested safety field")
    match ← must (AliasRuntime.solveGoal context 4096 100000 ⟨.positive,⟨identity,#[self,wrongTuple]⟩⟩) with
    | .noSolution => pure ()
    | _ => throw (IO.userError "nested unsafe FnPtr argument differs from rustc no-solution")
    count := count+1
  unless count==3 do throw (IO.userError "nested Fn-family count changed")
  let asyncDocument := (← must (decodeJson (← IO.FS.readFile asyncSource))).document
  let asyncOracle ← must (Json.parse (← IO.FS.readFile asyncOracle))
  unless ← must ((← must (asyncOracle.getObjVal? "proven")).getBool?) do
    throw (IO.userError "async closure control must be a real Rust FnOnce candidate")
  let asyncSelf ← must (GenericMaterialCodec.readTerm 4096 (← must (asyncOracle.getObjVal? "self")))
  let asyncTuple ← must (GenericMaterialCodec.readTerm 4096 (← must (asyncOracle.getObjVal? "args_tuple")))
  let fnOnce ← must (GenericMaterialCodec.readDefinition (← must (asyncOracle.getObjVal? "fn_once")))
  let #[declaration] := asyncDocument.traitProgram.traits.filter (·.definition==fnOnce)
    | throw (IO.userError "async FnOnce source declaration absent")
  let source : SourceFnTraits.Source := ⟨asyncDocument.definitions,asyncDocument.traitProgram,
    fun _ => throw "unexpected FnDef feature query in coroutine closure control"⟩
  match SourceFnTraits.query source Except.ok 4096 declaration #[asyncSelf,asyncTuple] with
  | .error "fn builtin coroutine closure requires async/coroutine source candidate provider" => pure ()
  | .error error => throw (IO.userError s!"wrong coroutine closure source boundary: {error}")
  | .ok _ => throw (IO.userError "unported coroutine closure became builtin absence or success")
  IO.println "PASS 3 nested FnPtr proofs across distinct JSON header order +3 real safety mismatches; actual Rust FnOnce coroutine closure stays explicit Unsupported"
