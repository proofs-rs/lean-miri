import duplicate_prefix.S05ZeroCellJointPacket
import Miri.Interpreter.RunLoop
import Lean
/-! Standalone native diagnostic; deliberately excluded from default Check.
Run with the fresh duplicate_prefix OLean directory on LEAN_PATH. The six
`rfl` equalities below kernel-check only the executable data aliases. `#eval`
observes the actual fixed interpreter; its output proves no execution fact.

This uses Machine.actualConfig capacity 1000001, corresponding exactly to
DuplicatePrefixArgumentCallResult.Result remaining 999999: Result.cfg adds one,
and PreparedContracts.actualConfig adds another. Every resource limit is
1000000. Resource adequacy for a kernel execution theorem is not asserted.
The input is the unchanged closed JointPacket, len=2/count=1, empty outer stack,
Shallow validation, initial Default retag mode, and Unit choice permitted by True.
Unknown bounds, Unsupported, fuel exhaustion and errors never count as return.
-/
open Lean Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open DuplicatePrefix
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option Elab.async false

-- Scratch-only compilation of the exact closed data expressions. No evaluator,
-- state, MIR, or interpreter operation is replaced.
open Lean Elab Command in
elab "executable_data " term:term " as " name:ident : command => do
  liftTermElabM do
    let expression ← instantiateMVars (← Term.elabTerm term none)
    let type ← Meta.inferType expression
    let env ← getEnv
    let expression ← Meta.deltaExpand expression (fun n => isNoncomputable env n || n == ``RootBody.reflected)
    let declaration := Declaration.defnDecl {name := name.getId,levelParams := [],type,value := expression,hints := .regular 0,safety := .safe}
    addDecl declaration
    compileDecl declaration

executable_data S05ZeroCellJointPacket.before as beforeData
executable_data RootBody.reflected as rootData
executable_data RootCompilerFacts.rootAbi as abiData
executable_data S05ZeroCellJointPacket.place as placeData
executable_data DuplicatePrefixSliceArgument.first PreparedReflection.actual.runtime.target.base S05ZeroCellJointPacket.argument 2 as firstData
executable_data EmptyRootArguments.second 1 as secondData
example : beforeData = S05ZeroCellJointPacket.before := rfl
example : rootData = RootBody.reflected := rfl
example : abiData = RootCompilerFacts.rootAbi := rfl
example : placeData = S05ZeroCellJointPacket.place := rfl
example : firstData = DuplicatePrefixSliceArgument.first PreparedReflection.actual.runtime.target.base S05ZeroCellJointPacket.argument 2 := rfl
example : secondData = EmptyRootArguments.second 1 := rfl

def budget : Nat := 1000000
def limits : ExecutionMachine.Limits := ⟨budget,budget,budget,budget⟩
def options : EvalConfigurationCore.Options :=
  Machine.exampleOptions limits budget budget budget 64 .Shallow ⟨false,false⟩

def describe (state : MachineHooks.State MiriMemoryKind Machine.RootUser) : String :=
  match state.stack.frames.back? with
  | none => "stack=empty"
  | some frame => s!"depth={state.stack.frames.size} body={frame.bodyIdentity.index} loc={reprStr frame.location}"

def walk (cfg : ExecutionMachine.Config MiriMemoryKind Machine.RootUser Unit Unit ABI.ExternAbi Unit)
    (fuel stepIndex : Nat) (state : MachineHooks.State MiriMemoryKind Machine.RootUser) : IO Unit := do
  match fuel with
  | 0 => IO.println s!"UNKNOWN step bound: {describe state}"
  | fuel+1 =>
    IO.println s!"STEP {stepIndex} {describe state}"
    let (after,outcome) := ExecutionMachine.step cfg limits () state
    match outcome with
    | .error error =>
      IO.println s!"ERROR step={stepIndex} kind={reprStr error} reportsUB={RunLoop.reportsUB error} after={describe after}"
    | .ok false => IO.println s!"STOP step={stepIndex} {describe after}"
    | .ok true => walk cfg fuel (stepIndex+1) after

def diagnostic : IO Unit := do
  IO.println "FINITE DIAGNOSTIC ONLY; not a safety proof"
  match Machine.actualConfig options () (budget+1) with
  | .error error => IO.println s!"CONFIG ERROR {reprStr error}"
  | .ok cfg =>
    IO.println "CONFIG ready"
    match Call.initStackFrame (ExecutionMachine.callHooks cfg limits) ()
        rootData.functionInstance rootData.body abiData
        #[.Copy firstData,.Copy secondData] false (.memory placeData) (.stop true)
        (⟨⟨#[]⟩,beforeData⟩ : MachineHooks.State MiriMemoryKind Machine.RootUser) with
    | .error error after => IO.println s!"INIT ERROR {reprStr error} reportsUB={RunLoop.reportsUB error} {describe after}"
    | .ok () installed =>
      IO.println s!"INIT OK {describe installed}"
      walk cfg 512 0 installed

#eval diagnostic
