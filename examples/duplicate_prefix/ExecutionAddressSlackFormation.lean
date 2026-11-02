import duplicate_prefix.GlobalAddressStackManagedFormation
import Miri.Interpreter.ExecutionAddressChoices
namespace DuplicatePrefix.ExecutionAddressSlackFormation
open Miri.ABI Miri.Memory Miri.Interpreter ExecutionChoices
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def consumed (tape : Tape) (selected : Fin 16) : Tape :=
  {tape with cursor:=tape.cursor+1,events:=tape.events.push ⟨.index .addressSlack 16,.index .addressSlack selected.val⟩}

/-- One raw supplied legal slack event drives the actual source index action.
No RNG seed, successful demand, or successful index action is an input. -/
theorem index {S} (access : Access S) (before : S) (selected : Fin 16)
    (supplied : (access.get before).inputs[(access.get before).cursor]?=some (.index .addressSlack selected.val)) :
    ExecutionChoices.index access .addressSlack 16 before=
      .ok selected.val (access.put before (consumed (access.get before) selected)) := by
  have bounded : (access.get before).cursor<(access.get before).inputs.size := by
    by_cases valid : (access.get before).cursor<(access.get before).inputs.size
    · exact valid
    · rw [Array.getElem?_eq_none (by omega)] at supplied
      cases supplied
  unfold ExecutionChoices.index
  unfold_internal ".ExecutionChoices.demand"
  unfold_internal ".ExecutionChoices.consume"
  simp only [show (16:Nat)≠0 from by decide,beq_iff_eq,Bool.false_eq_true,↓reduceIte,
    show ¬(access.get before).cursor>(access.get before).inputs.size from by omega,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    supplied,selected.isLt,beq_self_eq_true,Bool.not_true,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,consumed]
end DuplicatePrefix.ExecutionAddressSlackFormation
