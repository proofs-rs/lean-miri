import duplicate_prefix.CurrentCallCheckpointLenSource
import duplicate_prefix.CurrentCallCheckpointSharedBoolFrame
import duplicate_prefix.CurrentCallCheckpointLenFacts

namespace DuplicatePrefix.CurrentCallCheckpointRoot3
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows CandidateCurrentJointCall CurrentCallPostEntryCheckpoint
set_option autoImplicit false
noncomputable section

/-- One joint body output, on one actual root3 state. Source cells retain
their fixed origins; the scalar return resource keeps its independent bank.
The Shared and Len helpers have consumed two of the checkpoint's six slots. -/
structure Output {options remaining span len count place}
    (checkpoint : Checkpoint options remaining span len count place) (limits : ExecutionMachine.Limits) where
  result : CurrentCallCheckpointLenReturn.Result checkpoint limits
  source : CurrentCallCheckpointLenSource.Data checkpoint result
  target : CurrentCallCheckpointSharedBoolFrame.Packet checkpoint result

namespace Output
variable {options remaining span len count place limits}
    {checkpoint : Checkpoint options remaining span len count place} (out : Output checkpoint limits)

def machine : Before:=out.result.machine
def frame : CompilerFrameContext.ActualFrame:=out.result.rootFrame
def tracker (_out : Output checkpoint limits) : MachineHooks.BorrowState:=CurrentCallCheckpointLenControl.postTracker checkpoint

theorem tracked : out.machine.borrowTracker=some out.tracker:=out.result.tracked
theorem model : DuplicatePrefixCallModel.Model options remaining span out.machine:=CurrentCallCheckpointLenFacts.model checkpoint out.result
theorem origins : DuplicatePrefixTypeCacheOrigins.Origins out.machine.user.payload.payload.user.types:=CurrentCallCheckpointLenFacts.origins checkpoint out.result
theorem active : ∃thread,out.machine.threads.activeThread?=some thread ∧thread.topUserRelevantFrame=some 0:=out.result.active
theorem trace : SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
    (Storage.withCurrent #[] checkpoint.frame checkpoint.machine) (Storage.withCurrent #[] out.frame out.machine):=out.result.trace

theorem frameTracked : out.frame.extra.borrowTracker=some checkpoint.borrowFrame:=by
  change out.result.rootFrame.extra.borrowTracker=some checkpoint.borrowFrame
  rw [(CurrentCallCheckpointLenFacts.metadata checkpoint out.result).2.2.2.1,
    CurrentCallCheckpointSharedFacts.extra checkpoint out.result.frame out.result.shape out.result.base]
  exact checkpoint.frameTracked

theorem ledger : checkpoint.borrowFrame.protectedTags=
    #[(out.source.role.backing.id,out.source.node.tag),(out.target.current.id,out.target.current.node.tag)]:=by
  rw [out.source.id,out.source.nodeTag,out.target.id,out.target.tag]
  exact checkpoint.protectors

end Output

/-- The common continuation assembles its actual trace, full source bank,
physical copy readiness, and original Bool reservation internally. -/
theorem invoke {options remaining span len count place}
    (checkpoint : Checkpoint options remaining span len count place) (limits : ExecutionMachine.Limits)
    (budget : Nat) (dispatch : limits.callDispatch=budget+1) (nonzero : count≠0) :
    Nonempty (Output checkpoint limits):=by
  obtain ⟨result⟩:=CurrentCallCheckpointLenReturn.invoke checkpoint limits budget dispatch nonzero
  obtain ⟨source⟩:=CurrentCallCheckpointLenSource.of_return checkpoint result
  obtain ⟨target⟩:=CurrentCallCheckpointSharedBoolFrame.invoke checkpoint result
  exact ⟨⟨result,source,target⟩⟩

end
end DuplicatePrefix.CurrentCallCheckpointRoot3
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointRoot3" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved joint common root3 dependency {dependency}"
