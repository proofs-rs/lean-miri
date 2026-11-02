import Lean
import Miri.Interpreter.PlaceMachine

/-! Source proof that reading an initialized immediate scalar takes the actual
immediate branch of `MemoryOperand.readImmediate` and preserves the state when
the canonical retain hook has no touched allocation. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000

namespace DuplicatePrefix.ImmediateReadProof
open Miri.ABI Miri.Memory Miri.Interpreter

open Lean Elab Tactic in
elab "simp_immediate_read" : tactic => do
  let env ← getEnv
  let suffixes := ["Miri.Interpreter.PlaceMachine.commit",
    "Miri.Interpreter.PlaceMachine.finish",
    "Miri.Interpreter.isPrimitiveReadable"]
  let mut names := #[]
  for suffix in suffixes do
    let found := env.constants.toList.filterMap fun (name, _) =>
      if name.toString.endsWith suffix then some (mkIdent name) else none
    match found with
    | [name] => names := names.push name
    | _ => throwError "expected unique private source helper {suffix}"
  evalTactic (← `(tactic| simp_all [PlaceMachine.readImmediate,
    $[$names:ident],*, Miri.Interpreter.readImmediate,
    Miri.Interpreter.readImmediateRaw, localMemoryLayout,
    get, getThe, MonadStateOf.get, EStateM.get,
    set, MonadStateOf.set, EStateM.set, modify,
    modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet,
    Bind.bind, EStateM.bind, pure, EStateM.pure, Id.run]))

theorem read_scalar_immediate [DecidableEq K] [PointerProvenance Provenance]
    (config : PlaceMachine.AccessConfig K User)
    (state : MachineHooks.State K User) (scalar : Scalar Provenance)
    (layout : LocalLayout)
    (readable : ∃ value range, layout.layout.backendRepr =
      .Scalar (.Initialized (value := value) (validRange := range)))
    (retainNone : config.retainTouched state.machine none = state.machine) :
    PlaceMachine.readImmediate config ⟨.immediate (.scalar scalar), layout⟩ state =
      .ok ⟨.scalar scalar, layout⟩ state := by
  rcases readable with ⟨primitive, range, repr⟩
  simp_immediate_read

#print axioms read_scalar_immediate
end DuplicatePrefix.ImmediateReadProof
