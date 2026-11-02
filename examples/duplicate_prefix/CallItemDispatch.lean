import duplicate_prefix.RootCallCore
namespace DuplicatePrefix.CallItemDispatch
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
abbrev RootHooks := RootCallCore.RootHooks
noncomputable def itemStage (h : RootHooks) (fn : CallInstance) (abi : FnAbi TyId)
    (args : Array (FnArg Provenance)) (location : Bool) (destination : RuntimeStackPlace Provenance)
    (target : Option BasicBlockId) (unwind : UnwindAction) : CallM CanonicalConfigFacts.RootState (Option (CallRequest Provenance Unit ABI.ExternAbi (FnAbi TyId))) := do
  let found ← h.findMirOrEvalFn () fn abi args destination target unwind
  match found with
  | none => pure none
  | some (body, resolved) =>
    Call.initStackFrame h () resolved body abi args location destination (.goto target unwind)
    pure none
 theorem item_step (h : RootHooks) (fn : CallInstance) (definition : DefId) (abi : FnAbi TyId)
    (args : Array (FnArg Provenance)) (location : Bool) (destination : RuntimeStackPlace Provenance)
    (target : Option BasicBlockId) (unwind : UnwindAction) (callerAbi : ABI.ExternAbi)
    (kind : fn.kind = .Item definition) (canUnwind : h.abiCanUnwind abi = true)
    (rustCall : h.isRustCall callerAbi = false) :
    Call.initFnCallStep h () ⟨.Instance fn, callerAbi, some abi, args, location, destination, target, unwind⟩ =
      itemStage h fn abi args location destination target unwind := by
  simp [Call.initFnCallStep, kind, canUnwind, rustCall, itemStage]
  rfl
theorem dispatch_one (h : RootHooks) (request : CallRequest Provenance Unit ABI.ExternAbi (FnAbi TyId))
    (state next : CanonicalConfigFacts.RootState) (budget : Nat)
    (step : Call.initFnCallStep h () request state = .ok none next) :
    Call.initFnCall h () (budget + 1) request state = .ok () next := by
  simp only [Call.initFnCall, bind, EStateM.bind]
  rw [step]
  rfl
end DuplicatePrefix.CallItemDispatch
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.CallItemDispatch.item_step, ``DuplicatePrefix.CallItemDispatch.dispatch_one] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved call-dispatch dependency {dependency}"
