import Miri.Frontend.FoundationInput
import Miri.Input.EvalPreparation
import Miri.Input.CompilerForeignSymbols
open Lean Miri Miri.Interpreter Miri.Frontend.Foundation
private def checked {α : Type} (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def demand (table : Input.CompilerForeignSymbols.Prepared) (symbol : String)
    (access : Input.SourceCompilerWorld.Access (Option Input.SourceCompilerWorld.World)) :=
  Input.CompilerForeignSymbols.lookupFunction table (Input.CompilerCallPipeline.loadMir access) symbol
    (Input.CompilerForeignSymbols.resolveSource access)
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected actual custom foundation source")
  let decoded ← checked (decodeRunnerInputProfiled (← IO.FS.readFile path) {})
  let program ← checked (Input.lowerProgram decoded.document)
  let prepared ← checked (Input.EvalPreparation.prepareProfiled {} program).outcome
  let table ← checked prepared.compiler.foreignSymbols
  let some material := program.input.queries.runtime.foreignSymbols.sourceDeclarations
    | throw (IO.userError "raw source declarations were discarded")
  unless material.declarations.size == 231 && table.candidates.size == material.declarations.size do
    throw (IO.userError "actual complete declaration traversal changed")
  unless table.candidates.all (fun candidate => candidate.fnInstance.isNone && candidate.sourceDeclaration.isSome) do
    throw (IO.userError "foreign preparation allocated eager numeric identities")
  let world ← checked (Input.SourceCompilerWorld.create program.input)
  let access : Input.SourceCompilerWorld.Access (Option Input.SourceCompilerWorld.World) :=
    ⟨id,fun _ world => some world⟩
  let before := world.canonical.instances.size
  match (demand table "__foundation_absent_symbol_control" access).run (some world) with
  | .ok none (some after) =>
    unless after.canonical.instances.size == before do throw (IO.userError "symbol miss interned an unrelated function")
  | _ => throw (IO.userError "complete source symbol miss did not remain a miss")
  let some first := table.candidates[0]? | throw (IO.userError "actual source candidates empty")
  let some declaration := first.sourceDeclaration | throw (IO.userError "selected source declaration absent")
  let key ← checked (Input.CompilerSourceSymbols.monoKey declaration)
  let some retained := world.canonical.sourceMaterial | throw (IO.userError "typed universe missing")
  let missingMaterial := {retained with declarations := retained.declarations.filter (·.definition != key.definition)}
  let missingWorld := {world with canonical := {world.canonical with sourceMaterial := some missingMaterial}}
  match (demand table first.symbol access).run (some missingWorld) with
  | .error (.unsupported _) (some after) =>
    unless after.canonical.instances.size == before do
      throw (IO.userError "missing authoritative source declaration minted an identity")
  | _ => throw (IO.userError "missing authoritative source declaration was accepted")
  match (demand table first.symbol access).run (some world) with
  | .error (.unsupported _) (some after) =>
    unless after.canonical.instances.size == before + 1 do throw (IO.userError "selected source identity not interned exactly once")
    let some callee := Input.SourceCompilerWorld.findItem after key | throw (IO.userError "shared World lost selected key")
    let node ← checked (Input.SourceCompilerWorld.node after callee)
    unless node.kind == .identityOnly && node.bodyId.isNone do throw (IO.userError "foreign declaration fabricated executable MIR")
  | _ => throw (IO.userError "missing selected source body did not reject explicitly")
  match (demand table first.symbol access).run none with
  | .error (.unsupported _) none => pure ()
  | _ => throw (IO.userError "missing shared World silently created private identities")
  let strong := { first with crateName := "strong", weak := false }
  let weak := { first with crateName := "weak", weak := true }
  let policy := { table with candidates := #[weak,strong] }
  match Input.CompilerForeignSymbols.lookup policy first.symbol with
  | .ok (some chosen) => unless chosen.crateName == "strong" do throw (IO.userError "weak/strong winner changed")
  | _ => throw (IO.userError "weak/strong selection failed")
  match Input.CompilerForeignSymbols.lookup { table with candidates := #[strong,strong] } first.symbol with
  | .error (.machineStop _) => pure ()
  | _ => throw (IO.userError "equal-strength duplicate symbols accepted")
  let unsupported := { declaration with parameters := #[.typeParameter] }
  let unknown := { first with sourceDeclaration := some unsupported }
  match Input.CompilerForeignSymbols.lookup { table with candidates := #[unknown] } "unrelated" with
  | .error (.unsupported _) => pure ()
  | _ => throw (IO.userError "mono source prerequisite skipped before symbol comparison")
  IO.println "foreign provider: real 231 source declarations; no eager IDs; miss leaves World unchanged; selected identityOnly body rejects; missing World/mono/ambiguity reject; weak precedence preserved"
