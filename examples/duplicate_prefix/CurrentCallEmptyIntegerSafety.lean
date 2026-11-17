import duplicate_prefix.CurrentCallEmptyIntegerZeroSafety
import duplicate_prefix.CurrentCallEmptyIntegerNonzeroSafety
import duplicate_prefix.CurrentCallEmptyIntegerBodyControl
import duplicate_prefix.CurrentCallEmptyIntegerCounterFrame
import duplicate_prefix.CurrentCallEmptyIntegerEntryFacts
import duplicate_prefix.CurrentCallEmptyIntegerCurrent
import duplicate_prefix.CurrentCallResourceSingleBoolRelease
import duplicate_prefix.CurrentCallResourceRootFinish
import duplicate_prefix.DuplicatePrefixArgumentCallResult
import duplicate_prefix.PushThread
namespace DuplicatePrefix.CurrentCallEmptyIntegerSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
open TypedBorrowSteps ReferenceBorrowDriver ReturnProtection CurrentCallEmptyTypedEntry GeneralBorrowFnEntryRegistration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section
theorem invoke (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState)
    (model : DuplicatePrefixCallModel.Model options remaining span before)
    (enabled : before.borrowTracker=some tracker)
    (stackReady : CurrentCallPush.StackReadiness before #[])
    (address count : UInt64) (nonzero : address≠0)
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow before place)
    (data : Identities) (owner : Nat)
    (B : UniformWindow before tracker data owner physical.id physical.offset.toNat 1 .ret)
    (pointer : physical.pointer=B.pointer.value) (allocation : physical.entry.allocation=B.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (binding : CandidateCallBindings.WindowBinding before physical.pointer physical.id physical.offset.toNat 1)
    (distinct : B.allocation.extra.roots.toList.Nodup)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+3<18446744073709551615)
    (nodeRoom : B.allocation.extra.nodes.size+1<65536)
    (ready : CurrentCallBoolProtection.WindowReady before physical.id physical.offset.toNat 1)
    (dynamicFuel validationFuel : Nat)
    (dynamicEq : options.place.dynamicFuel=dynamicFuel+1)
    (validationEq : options.limits.validation=validationFuel+1)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins before.user.payload.payload.user.types)
    (budget : Nat) (dispatchEq : limits.callDispatch=budget+1) :


    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.integer address) 0 count place := by
  by_cases zero : count=0
  · subst count
    exact CurrentCallEmptyIntegerZeroSafety.invoke options limits remaining span before tracker model enabled stackReady address nonzero place physical
      data owner B pointer allocation runtime binding distinct (by omega) nodeRoom ready dynamicFuel validationFuel dynamicEq validationEq origins
  · exact CurrentCallEmptyIntegerNonzeroSafety.invoke options limits remaining span before tracker model enabled stackReady address count zero nonzero place physical
      data owner B pointer allocation runtime binding distinct tagRoom nodeRoom ready dynamicFuel validationFuel dynamicEq validationEq origins budget dispatchEq
end
end DuplicatePrefix.CurrentCallEmptyIntegerSafety
