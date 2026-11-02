import duplicate_prefix.ExecutionAddressSlackFormation
namespace DuplicatePrefix.ExecutionIndexNumericFormation
open Miri.ABI Miri.Memory Miri.Interpreter ExecutionChoices
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def consumed (tape : Tape) (site : IndexSite) (count selected : Nat) : Tape :=
  {tape with cursor:=tape.cursor+1,events:=tape.events.push ⟨.index site count,.index site selected⟩}

/-- A raw in-support selected index and supplied typed event execute the
actual source draw, including its event log and cursor update. -/
theorem index {S} (access : Access S) (before : S) (site : IndexSite) (count selected : Nat)
    (within : selected<count)
    (supplied : (access.get before).inputs[(access.get before).cursor]?=some (.index site selected)) :
    ExecutionChoices.index access site count before=
      .ok selected (access.put before (consumed (access.get before) site count selected)) := by
  have bounded : (access.get before).cursor<(access.get before).inputs.size := by
    by_cases valid : (access.get before).cursor<(access.get before).inputs.size
    · exact valid
    · rw [Array.getElem?_eq_none (by omega)] at supplied
      cases supplied
  unfold ExecutionChoices.index
  unfold_internal ".ExecutionChoices.demand"
  unfold_internal ".ExecutionChoices.consume"
  simp only [show count≠0 from by omega,beq_iff_eq,Bool.false_eq_true,↓reduceIte,
    show ¬(access.get before).cursor>(access.get before).inputs.size from by omega,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    supplied,within,beq_self_eq_true,Bool.not_true,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,consumed]
end DuplicatePrefix.ExecutionIndexNumericFormation
