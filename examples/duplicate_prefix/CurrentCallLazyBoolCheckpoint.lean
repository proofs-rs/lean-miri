import duplicate_prefix.CurrentCallLazyBoolSourceFrame

/-! The latent-Bool branch produces the SAME source/return resource interfaces
used by the post-entry continuation. This is an actual protection-stage adapter,
not yet a proof of the surrounding initStackFrame or original strong Result. -/
namespace DuplicatePrefix.CurrentCallLazyBoolCheckpoint
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallSpatialCover CurrentCallPostEntryCheckpoint
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

theorem protect (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (retagCtx : ActualRetagContext.Context options remaining span)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (machine : Before) (tracker : MachineHooks.BorrowState) (start : Nat) (len : UInt64)
    (source : Source machine tracker start len) (copyReady : CopyReady source)
    (family : Family) (root : BorTag) (image : Allocation CtfeProvenance Unit)
    (base offset : UInt64) (place : MPlaceTy Provenance)
    (ready : CurrentCallLazyBoolEnsure.Ready options (Storage.withCurrent frames frame machine) tracker family root image base offset place)
    (noFunction : machine.memory.hasFunctionPointer family.allocation=false)
    (noVaList : machine.memory.hasVaListId family.allocation=false)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (ghost : machine.user.payload.ghost=false) (backend : machine.user.payload.payload.user.backend=.none) :
    ∃post : RootState, ∃output : Return post.machine
        (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag) place,
      ∃current : Source post.machine (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag) start len,
      CopyReady current ∧current.tag≠output.node.tag ∧output.window.allocation.extra.nodes.size≤2 ∧
      TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag options.limits.retag place
        (Storage.withCurrent frames frame machine)=.ok () post ∧
      current.role.family=source.role.family ∧current.role.backing.allocation=source.role.backing.allocation ∧
      HEq current.role.backing.cells source.role.backing.cells ∧
      output.id=family.allocation ∧output.offset=offset.toNat ∧output.original=family.at allocationRoot ∧
      post.machine.borrowTracker=some (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag) ∧
      post.stack=(Storage.withCurrent frames (registeredFrame frame borrowFrame family.allocation tracker.global.nextPointerTag) machine).stack ∧
      post.machine={MemoryExtras.putAllocation (GlobalDataOnlyActualConfig.extras options) machine family.allocation ⟨none,#[]⟩ with
        memory:={machine.memory with live:=((machine.memory.live.filter (fun row=>row.1!=family.allocation)).push (family.allocation,⟨.machine .global,output.window.allocation⟩))},
        borrowTracker:=some (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag)} := by
  obtain ⟨post,output,newCtx,current,actual,familyEq,allocationEq,cellsEq,idEq,offsetEq,originalEq,outputTag,outputNodes,tracked,stack,machineEq,addresses,live,extras⟩:=
    CurrentCallLazyBoolSourceFrame.protect_with_source options remaining span retagCtx frames frame borrowFrame frameBorrow
      machine tracker source.context start len.toNat source.role source.runtime family root image base offset place ready
      noFunction noVaList fresh ghost backend
  have currentId : current.backing.id=source.role.backing.id:=
    current.id.symm.trans ((congrArg Family.allocation familyEq).trans source.role.id)
  have different : source.role.backing.id≠family.allocation := by
    obtain ⟨entry,address,present,_⟩:=source.binding
    intro same
    have missing:=ready.absent
    change machine.memory.live.find? (fun row=>row.1==family.allocation)=none at missing
    rw [same] at present
    rw [present] at missing
    cases missing
  have currentRuntime : DuplicatePrefixBorrowContract.RuntimeFacts current.backing.allocation.extra
      (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag) := by
    rw [allocationEq]
    have after:=(GeneralBorrowFnEntryRegistrationRuntime.prepare source.role.backing.allocation.extra tracker.global
      borrowFrame family.allocation fresh source.runtime).2.2.2.1
    simpa only [GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,
      registeredGlobal,allocatedTracker,ite_true] using after
  have binding : CandidateCallBindings.WindowBinding post.machine current.family.value current.backing.id start len.toNat := by
    rw [familyEq,currentId]
    exact CurrentCallOtherAllocationWindow.binding source.binding family.allocation
      ⟨.machine .global,output.window.allocation⟩ (Ne.symm different) live addresses
  let next : Source post.machine (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag) start len := {
    context:=newCtx,role:=current,runtime:=currentRuntime,
    distinct:=by rw [allocationEq];exact source.distinct,
    tag:=source.tag,concrete:=by rw [familyEq,currentId];exact source.concrete,
    grant:=source.grant,node:=source.node,nodeAt:=by rw [allocationEq];exact source.nodeAt,
    nodeTag:=source.nodeTag,hidden:=source.hidden,
    activity:=by rw [allocationEq];exact source.activity,
    binding:=binding,positive:=source.positive,signedFits:=source.signedFits,
    nodes:=by rw [allocationEq];exact source.nodes}
  have nextReady : CopyReady next := by
    refine ⟨?_,?_⟩
    · change CurrentCallResourceEntrySourceStorage.Data current.backing.allocation (UInt64.ofNat start) len
      rw [allocationEq];exact copyReady.storage
    · change CurrentCallBoolProtection.WindowReady post.machine current.backing.id start len.toNat
      rw [currentId]
      exact CurrentCallOtherAllocationWindow.ready copyReady.profile family.allocation ⟨none,#[]⟩ (Ne.symm different) extras
  have tagsDifferent : next.tag≠output.node.tag := by
    have older:=GeneralBorrowParentTagInvariant.parent_below_fresh source.role.backing.allocation.extra tracker.global
      source.runtime source.grant source.node source.nodeAt
    rw [source.nodeTag] at older
    intro equal
    change source.tag=output.node.tag at equal
    rw [outputTag] at equal
    rw [equal] at older
    exact UInt64.lt_irrefl _ older
  exact ⟨post,output,next,nextReady,tagsDifferent,outputNodes,actual,familyEq,allocationEq,cellsEq,idEq,offsetEq,originalEq,tracked,stack,machineEq⟩

end
end DuplicatePrefix.CurrentCallLazyBoolCheckpoint
