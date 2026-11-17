import duplicate_prefix.CurrentCallEmptyMissEntry
import duplicate_prefix.CurrentCallEmptyNoSourceFacts
namespace DuplicatePrefix.CurrentCallEmptyMissFacts
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
open CurrentCallEmptyTypedEntry
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
variable (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState) (root : RootFrame) (address count : UInt64)
    (id : AllocId) (tag : BorTag)
    (miss : before.user.addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup before.memory)=.ok none)

def effect : Effect options before tracker (.pointer (Pointer.new .wildcard (Size.ofBytes address))) := .miss address miss

def args := CurrentCallEmptyNoSourceFacts.args options remaining span before tracker
  (.pointer (Pointer.new .wildcard (Size.ofBytes address))) (effect options before tracker address miss) root count

def frame := CurrentCallEmptyNoSourceFacts.frame options remaining span before tracker
  (.pointer (Pointer.new .wildcard (Size.ofBytes address))) (effect options before tracker address miss) root count id tag

def value := CurrentCallEmptyNoSourceFacts.value options remaining span (.pointer (Pointer.new .wildcard (Size.ofBytes address)))

theorem locals_eq :
    (frame options remaining span before tracker root address count id tag miss).locals=
      (PositiveRootInstalledFrame.installed root (value options remaining span address) count {} id tag id tag).locals := by
  exact CurrentCallEmptyNoSourceFacts.locals_eq options remaining span before tracker
    (.pointer (Pointer.new .wildcard (Size.ofBytes address))) (effect options before tracker address miss) root count id tag rfl

theorem metadata :
    let f:=frame options remaining span before tracker root address count id tag miss
    f.body=root.frame.body ∧ f.bodyIdentity=root.frame.bodyIdentity ∧ f.functionInstance=root.frame.functionInstance ∧
    f.returnContinuation=root.frame.returnContinuation ∧ f.returnPlace=root.frame.returnPlace ∧ f.vaList=root.frame.vaList ∧
    f.extra.dataRace=root.frame.extra.dataRace ∧ f.extra.borrowTracker=some (({} : FrameState).addProtector id tag) ∧
    f.location=.mir ⟨0,0⟩ := by
  exact CurrentCallEmptyNoSourceFacts.metadata options remaining span before tracker
    (.pointer (Pointer.new .wildcard (Size.ofBytes address))) (effect options before tracker address miss) root count id tag rfl

theorem zero_prefix
    (limits : ExecutionMachine.Limits)
    (raw : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (machine : Before) (model : DuplicatePrefixCallModel.Model options remaining span machine)
    (fuel : Nat) (fuelEq : options.limits.validation=fuel+1) :
    let f:=frame options remaining span before tracker root address 0 id tag miss
    ∃ result : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits (Storage.withCurrent #[] f machine)
        (Storage.withCurrent #[] result (RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span machine))) ∧
      result.body=RootBody.reflected.body.body ∧ result.bodyIdentity=RootBody.reflected.body.identity ∧
      result.functionInstance=RootBody.reflected.functionInstance ∧ result.locals.size=25 ∧ result.location=.mir ⟨10,0⟩ ∧
      result.locals[0]?=some ⟨.live (.immediate (.scalar (.fromBool true))),some RootCompilerFacts.boolLayout⟩ ∧
      result.returnPlace=f.returnPlace ∧ result.extra=f.extra ∧ result.returnContinuation=f.returnContinuation ∧
      result.vaList=f.vaList ∧ CopyHelperCleanup.AllImmediate result := by
  exact CurrentCallEmptyNoSourceFacts.zero_prefix options remaining span before tracker
    (.pointer (Pointer.new .wildcard (Size.ofBytes address))) (effect options before tracker address miss) root id tag rfl limits raw machine model fuel fuelEq

end
end DuplicatePrefix.CurrentCallEmptyMissFacts
