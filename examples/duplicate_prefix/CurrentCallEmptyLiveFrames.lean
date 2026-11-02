import duplicate_prefix.CurrentCallEmptySourceArguments
import duplicate_prefix.PositiveRootInstalledFrame
namespace DuplicatePrefix.CurrentCallEmptyLiveFrames
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
open CurrentCallEmptyTypedEntry TypedBorrowSteps
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
private theorem root_ext {first second : RootFrame} (same : first.frame=second.frame) : first=second := by
  cases first
  cases second
  cases same
  rfl

def adjusted {options before tracker argument} (effect : Effect options before tracker argument)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) : Immediate Provenance :=
  (DuplicatePrefixSliceArgument.rawValue (config options remaining span).access.runtime.base effect.output 0 ActualReferenceMetadata.reference).imm

/-- The actual empty source constructor installs its concrete output value and
registers its real zero-byte protector. This is a pure frame identity. -/
theorem live_root {options before tracker argument} (effect : Effect options before tracker argument)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (root : RootFrame) (borrowFrame : FrameState)
    (sourceId : AllocId) (allocated : effect.allocation=some sourceId) :
    CurrentCallEmptySourceArguments.doneRoot effect remaining span root borrowFrame=
      PositiveRootArguments.firstDone root (adjusted effect remaining span) borrowFrame sourceId tracker.global.nextPointerTag := by
  apply root_ext
  simp only [CurrentCallEmptySourceArguments.doneRoot,CurrentCallEmptyTypedEntry.resultFrame,allocated,
    CurrentCallEmptyTypedEntry.registered,CurrentCallEmptyTypedEntry.copied,CurrentCallEmptyReferenceValidation.writtenFrame,
    PositiveRootArguments.firstDone,PositiveRootArguments.protectedRoot,registeredFrame,TypedRetagEntry.frameWithBorrow,
    firstLive,firstCache,live,write,cache,atSpan,LocalOperands.cachedLayoutFrame,Array.set_set,Array.getElem_set_self,i1,adjusted]

def finishedFrame {options before tracker argument} (effect : Effect options before tracker argument)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (root : RootFrame) (count : UInt64)
    (borrowFrame : FrameState) (sourceId boolId : AllocId) (boolTag : BorTag) :=
  CallEntryFacts.doneRootFrame
    {registeredFrame (atSpan (RootArgumentsTwo.result (CurrentCallEmptySourceArguments.doneRoot effect remaining span root borrowFrame) count) ⟨601⟩).frame
      (borrowFrame.addProtector sourceId tracker.global.nextPointerTag) boolId boolTag with location:=.unwinding ⟨559⟩}

/-- Both actual ABI arguments, source zero protector and Bool protector have
the existing installed-frame shape, with the exact original return place. -/
theorem installed_eq {options before tracker argument} (effect : Effect options before tracker argument)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (root : RootFrame) (count : UInt64)
    (borrowFrame : FrameState) (sourceId boolId : AllocId) (boolTag : BorTag) (allocated : effect.allocation=some sourceId) :
    finishedFrame effect remaining span root count borrowFrame sourceId boolId boolTag=
      PositiveRootInstalledFrame.installed root (adjusted effect remaining span) count borrowFrame sourceId tracker.global.nextPointerTag boolId boolTag := by
  unfold finishedFrame
  rw [live_root effect remaining span root borrowFrame sourceId allocated]
  rfl
end
end DuplicatePrefix.CurrentCallEmptyLiveFrames
