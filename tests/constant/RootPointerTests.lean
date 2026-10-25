import Miri.Input.Decoder
import Miri.Interpreter.Constant
open Miri Input Memory ABI Interpreter
private def must (v : Except String A) : IO A := match v with | .ok a => pure a | .error e => throw (IO.userError e)
private def check (c : Bool) (message : String) : IO Unit := unless c do throw (IO.userError message)
private def queries (failAdjust : Bool) : ConstantQueries CtfeProvenance Unit Unit (Array String) := {
  instantiateAndNormalize := fun _ _ => throw (.query "synthetic root routing fixture has no normalization query")
  evaluate := fun _ _ _ => throw (.query "synthetic root routing fixture has no evaluation query")
  adjustGlobalRootPointer := fun pointer => do
    let state ← EStateM.get
    EStateM.set { state with hooks := state.hooks.push "adjust-root" }
    if failAdjust then throw (.query "machine root adjustment failed")
    pure pointer
  externStaticPointer := fun definition => do
    let state ← EStateM.get
    EStateM.set { state with hooks := state.hooks.push s!"extern:{definition}" }
    let some global := state.memory.globals[0]? | throw (.query "missing synthetic extern result")
    let prov ← match CtfeProvenance.fromAllocId global.allocId with
      | .ok p => pure p
      | .error _ => throw (.query "invalid synthetic extern provenance")
    pure (.new prov .ZERO)
}
def main (args : List String) : IO Unit := do
  let path ← match args with | p :: _ => pure p | [] => throw (IO.userError "expected compiler metadata fixture")
  let doc ← must (decodeJson (← IO.FS.readFile path))
  let runtime ← must ((RuntimeMetadata.ofDocument doc.document).mapError toString)
  let program ← must (lowerProgram doc.document)
  let fnInstance : CallInstance := ⟨.Item (← must (program.rootDefinitionId 0)), #[]⟩
  let some ty := doc.document.types.find? (fun t => t.layout.sizeBytes == some 8 && (t.shapeKind == .reference || t.shapeKind == .rawPointer))
    | throw (IO.userError "fixture lacks pointer layout")
  let makeState (tls foreign : Bool) : Except String (ConstantState CtfeProvenance Unit Unit (Array String)) := do
    let initial : MemoryState CtfeProvenance Unit Unit := { MemoryState.empty with nextAllocId := 100 }
    let registered := MemoryLifecycle.registerImportedGlobal initial () 0 .static (.ofBytes 8) .ONE .Not
      (some (.static 22 true tls foreign))
    let _ ← registered.outcome.mapError toString
    pure ⟨registered.memory, #[], fnInstance⟩
  let tls ← must (makeState true false)
  match constValueToOp runtime (queries false) (.Scalar (.Ptr (.Allocation 0 0 false false))) ty.id tls with
  | .error (.tlsConstantPointer _) after => check after.hooks.isEmpty "TLS reached machine root hook"
  | _ => throw (IO.userError "TLS constant pointer was accepted")
  let foreign ← must (makeState false true)
  match constValueToOp runtime (queries false) (.Scalar (.Ptr (.Allocation 0 5 false false))) ty.id foreign with
  | .ok _ after => check (after.hooks == #["extern:22"]) "extern static used normal root adjustment"
  | .error e _ => throw (IO.userError (reprStr e))
  let normal ← must (makeState false false)
  match constValueToOp runtime (queries true) (.Scalar (.Ptr (.Allocation 0 0 false false))) ty.id normal with
  | .error (.query _) after => check (after.hooks == #["adjust-root"]) "failed machine root hook effects were rolled back"
  | _ => throw (IO.userError "machine root adjustment failure became success")
  let missing := { normal with memory := MemoryState.empty }
  match constValueToOp runtime (queries false) (.Scalar (.Ptr (.Allocation 0 0 false false))) ty.id missing with
  | .error (.metadata _) after => check after.hooks.isEmpty "missing source identity reached root adjustment"
  | _ => throw (IO.userError "missing global identity became success")
  IO.println "constant root routing passed: TLS rejected before hooks, extern hook selected, failed-hook effects retained, missing mapping rejected"
