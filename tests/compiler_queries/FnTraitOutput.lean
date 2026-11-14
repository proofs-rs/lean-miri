import Miri.Input.Decoder
import Miri.Input.SourceFnTraits
import Miri.Input.AliasRuntime
open Lean Miri.Input GenericSubstitution
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error e => throw (IO.userError e)

/-- Signature payloads encode JSON objects; object key order is not type data.
Canonicalize serialization only, retaining every key/value and all identities. -/
private def canonicalHeaders : Nat → GenericSubstitution.Term → Except String GenericSubstitution.Term
  | 0,_ => throw "signature payload canonicalization exhausted"
  | fuel+1,term => do
    match term with
    | .node .aggregate "signature" payload children =>
      let payload ← Json.parse payload
      return .node .aggregate "signature" payload.compress (← children.mapM (canonicalHeaders fuel))
    | .node sort tag payload children => return .node sort tag payload (← children.mapM (canonicalHeaders fuel))
    | .definition sort tag identity children => return .definition sort tag identity (← children.mapM (canonicalHeaders fuel))
    | .binder variables body => return .binder variables (← canonicalHeaders fuel body)
    | _ => pure term

def checkNovel (sourcePath oraclePath : String) : IO Unit := do
  let document := (← must (decodeJson (← IO.FS.readFile sourcePath))).document
  let context ← must (AliasRuntime.Context.ofDocument document)
  let oracle ← must (Json.parse (← IO.FS.readFile oraclePath))
  let rows ← must ((← must (oracle.getObjVal? "queries")).getArr?)
  unless rows.size==11 do throw (IO.userError "Fn source callable corpus changed")
  let attributes ← rows.foldlM (fun result row => do
    let self ← must (GenericMaterialCodec.readTerm 4096 (← must (row.getObjVal? "self")))
    let .definition .type "function_definition" identity _ := self | pure result
    let names ← must (((← must (row.getObjVal? "raw_target_features")).getArr?).bind fun values => values.mapM Json.getStr?)
    pure (result.push (identity,names))) (#[] : Array (DefinitionIdentity × Array String))
  let source : SourceFnTraits.Source := ⟨document.definitions,document.traitProgram,fun identity => do
    let matchingRows := attributes.filter (·.1==identity)
    let #[(_identity,names)] := matchingRows | throw "FnDef raw target features absent or ambiguous"
    pure names⟩
  let normalize := AliasRuntime.normalizeTerm context 100000 16384 #[] #[]
  let mut positive := 0
  let mut negative := 0
  let mut projections := 0
  let mut wrongArgs := 0
  let mut obligationGuards := 0
  for row in rows do
    let self ← must (GenericMaterialCodec.readTerm 4096 (← must (row.getObjVal? "self")))
    let tuple ← must (GenericMaterialCodec.readTerm 4096 (← must (row.getObjVal? "args_tuple")))
    let family ← must ((← must (row.getObjVal? "family")).getStr?)
    let goals ← must ((← must (row.getObjVal? "goals")).getArr?)
    for goal in goals do
      let identity ← must (GenericMaterialCodec.readDefinition (← must (goal.getObjVal? "definition")))
      let expected ← must ((← must (goal.getObjVal? "proven")).getBool?)
      let #[declaration] := document.traitProgram.traits.filter (·.definition==identity)
        | throw (IO.userError "Fn source trait declaration absent")
      let result ← must (SourceFnTraits.query source normalize 4096 declaration #[self,tuple])
      let candidateProven ← if let some candidate := result then do
          let hooks := AliasRuntime.traitHooks context 4096 (fun universeIndex remaining goals term =>
            AliasRuntime.normalizeTermScoped context universeIndex 100000 remaining #[] goals term)
          match ← must (TraitSelection.fulfill document.traitProgram hooks {eraseRegions := true}
              4096 100000 candidate.obligations) with
          | .proven _ => pure true
          | .noSolution => pure false
          | .ambiguous reason => throw (IO.userError s!"Fn source nested obligations ambiguous: {reason}")
        else pure false
      unless candidateProven==expected do throw (IO.userError "Fn source candidate plus obligations disagrees with actual rustc selection")
      if expected then
        let some result := result | throw (IO.userError "actual Fn candidate absent")
        let expectedOutput ← must (GenericMaterialCodec.readTerm 4096 (← must (goal.getObjVal? "output")))
        unless result.output==expectedOutput do throw (IO.userError "Fn source Output differs from actual rustc normalization")
        positive := positive+1
      else negative := negative+1
      if family != "fn_definition" then
        let outcome ← must (AliasRuntime.solveGoal context 4096 100000 ⟨.positive,⟨identity,#[self,tuple]⟩⟩)
        match outcome with
        | .proven _ => unless expected do throw (IO.userError "Fn builtin engine proved false callable")
        | .noSolution => unless !expected do throw (IO.userError "Fn builtin engine rejected actual callable")
        | .ambiguous reason => throw (IO.userError s!"ground Fn builtin engine ambiguous: {reason}")
      if declaration.builtin==some .fnOnce then
        let wrong := Term.node .type "tuple" "" (Terms.ofArray #[.atom .type "uint" "u8"])
        unless (← must (SourceFnTraits.query source normalize 4096 declaration #[self,wrong])).isNone do
          throw (IO.userError "Fn source candidate ignored Args tuple relation")
        wrongArgs := wrongArgs+1
        if expected && family != "fn_definition" then
          let output ← must (GenericMaterialCodec.readDefinition (← must (row.getObjVal? "output_definition")))
          let projection := Term.definition .type "alias_projection_not_rigid" output (Terms.ofArray #[self,tuple])
          let actual ← must (normalize projection)
          let expectedOutput ← must (GenericMaterialCodec.readTerm 4096 (← must (goal.getObjVal? "output")))
          unless actual==expectedOutput do throw (IO.userError "Fn builtin alias reduction differs from actual rustc Output")
          let definitions := context.generic.definitions.map fun definition =>
            if definition.crateIndex==output.crateIndex && definition.index==output.index then
              {definition with sourceEnvironment := definition.sourceEnvironment.map fun scope =>
                {scope with ownPredicates := scope.ownPredicates.push ⟨#[],.equal (.atom .type "uint" "u8") (.atom .type "uint" "u16")⟩}}
            else definition
          let bad := {context with generic := {context.generic with definitions}}
          match AliasRuntime.normalizeTerm bad 100000 16384 #[] #[] projection with
          | .error "alias normalization own predicates have no solution" => pure ()
          | .error error => throw (IO.userError s!"wrong Fn Output obligation residual: {error}")
          | .ok _ => throw (IO.userError "Fn builtin projection dropped Output own predicates")
          obligationGuards := obligationGuards+1
          projections := projections+1
  unless positive==12 && negative==21 && projections==4 && wrongArgs==11 && obligationGuards==4 do
    throw (IO.userError s!"Fn source controls changed: {positive}/{negative}/{projections}/{wrongArgs}")
  IO.println "PASS 33 actual callable Fn goals:12positive21negative incl3OutputSized failures;4real builtin Output projections;11Args mismatch controls;4Output own-predicate guards"

def checkStd (sourcePath oraclePath : String) : IO Unit := do
  let document := (← must (decodeJson (← IO.FS.readFile sourcePath))).document
  let context ← must (AliasRuntime.Context.ofDocument document)
  let some node := document.types[803]? | throw (IO.userError "actual std FnDef803 absent")
  let .functionDefinition physical arguments _ _ _ := node.shape
    | throw (IO.userError "actual std type803 is not FnOnce FnDef")
  let some definition := document.definitions[physical]? | throw (IO.userError "std FnDef physical definition absent")
  let some template := definition.genericTemplate | throw (IO.userError "std FnDef raw signature absent")
  let arena ← must (TypeArena.World.ofMaterial document.types document.typeConstants document.definitions
    document.predicates context.generic.pointerBytes)
  let arguments ← must (GenericInstantiationWorld.ofArguments arena 16384 arguments)
  let oracle ← must (Json.parse (← IO.FS.readFile oraclePath))
  let expectedSelf ← must (GenericMaterialCodec.readTerm 16384 (← must (oracle.getObjVal? "self")))
  let some actualSelf := arguments[0]? | throw (IO.userError "std Self absent")
  unless (← must (canonicalHeaders 16384 actualSelf))==(← must (canonicalHeaders 16384 expectedSelf)) do
    IO.FS.writeFile "scratch/fn-trait-output-next/actual-std-self.txt" (reprStr arguments[0]?)
    IO.FS.writeFile "scratch/fn-trait-output-next/expected-std-self.txt" (reprStr (some expectedSelf))
    throw (IO.userError "actual std oracle closure differs from exact Type138 input")
  let expectedSignature ← must (GenericMaterialCodec.readTerm 16384 (← must (oracle.getObjVal? "normalized_signature")))
  let raw ← must (template.instantiateSignature 16384 arguments)
  let expectedMethod ← must (GenericMaterialCodec.readDefinition (← must (oracle.getObjVal? "method_definition")))
  unless definition.crateIndex==expectedMethod.crateIndex && definition.index==expectedMethod.index do
    throw (IO.userError "std test FnDef is not the physical FnOnce call_once")
  let expectedOutput ← must (GenericMaterialCodec.readDefinition (← must (oracle.getObjVal? "output_definition")))
  let rawSignature ← must (RawFunctionSignature.read raw)
  let .definition .type "alias_projection_not_rigid" outputIdentity _ := rawSignature.output
    | throw (IO.userError "std original signature has no FnOnce Output projection")
  unless outputIdentity==expectedOutput do throw (IO.userError "std original signature projects another physical member")
  let normalized ← must (AliasRuntime.normalizeTerm context 100000 16384 #[] #[] raw)
  unless (← must (canonicalHeaders 16384 normalized))==(← must (canonicalHeaders 16384 expectedSignature)) do throw (IO.userError "actual std FnDef803 normalized signature differs from independent rustc")
  let signature ← must (RawFunctionSignature.read normalized)
  unless signature.inputs.size==2 && signature.abi==.RustCall && signature.output==.atom .type "int" "isize" do
    throw (IO.userError "actual std FnDef803 Output normalization differs from closure synthetic signature")
  IO.println "PASS actual std FnDef803 FnOnce closure138 Output normalized from synthetic signature to isize;2RustCall inputs"

def main (args : List String) : IO Unit := do
  if let ["std",source,oracle] := args then return ← checkStd source oracle
  let [source,oracle,std,stdOracle] := args | throw (IO.userError "expected novel raw source oracle and actualstd input")
  checkNovel source oracle
  checkStd std stdOracle
