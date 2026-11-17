import duplicate_prefix.CurrentCallResourceEmptyRootRelease
import duplicate_prefix.CurrentCallEmptyEntrySourceData
import duplicate_prefix.CurrentCallBodyPrefix
import duplicate_prefix.CurrentCallResourceRootFinish
namespace DuplicatePrefix.CurrentCallEmptyLiveZeroFinish
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext RootFrameData
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
private theorem tick_model (options remaining span machine)
    (model : DuplicatePrefixCallModel.Model options remaining span machine) :
    DuplicatePrefixCallModel.Model options remaining span (RootZeroCompleteState.tick options remaining span machine) := by
  have flags:=RootZeroCompleteState.tick_flags options remaining span machine
  have unchecked:=model.unchecked
  have noGc:=model.noGc
  rw [(actual_fields options () (remaining+1) span).terminators] at unchecked noGc
  unfold RootZeroCompleteState.tick SourceControl.accounted at flags ⊢
  rw [(actual_fields options () (remaining+1) span).terminators] at flags ⊢
  exact {model with
    unchecked:=by rw [(actual_fields options () (remaining+1) span).terminators];exact flags.1.trans unchecked
    noGc:=by rw [(actual_fields options () (remaining+1) span).terminators];exact flags.2.trans noGc}

/-- Shared count-zero suffix for actual live empty source entry. The source
has only an inactive zero-byte node, never a positive source resource. -/
theorem finish {initial oldTracker oldData oldOwner boolId boolOffset machine tracker data owner}
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (place : MPlaceTy Provenance)
    (original : UniformWindow initial oldTracker oldData oldOwner boolId boolOffset 1 .ret)
    (B : UniformWindow machine tracker data owner boolId boolOffset 1 .ret)
    (physical : CurrentCallBoolScalarWrite.Window machine place)
    (binding : CandidateCallBindings.WindowBinding machine physical.pointer physical.id physical.offset.toNat 1)
    (sameId : physical.id=boolId) (sameOffset : physical.offset.toNat=boolOffset)
    (samePointer : physical.pointer=original.pointer.value) (sameAllocation : physical.entry.allocation=B.allocation)
    (parentIssued : SpatialDelegation machine tracker boolId B.allocation B.precise.completion original.pointer.grant)
    (parentBinding : PointerBinds B.allocation original.pointer)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (distinct : B.allocation.extra.roots.toList.Nodup) (short : B.allocation.extra.nodes.size<65536)
    (concrete : ∃ supplied tag,B.pointer.value.provenance=.concrete supplied tag)
    (node : TreeNode) (nodeAt : B.allocation.extra.nodes.get B.pointer.grant=some node) (hidden : node.isExposed=false)
    (activeB : GeneralBorrowFreshActiveWithin.ActiveWithin B.allocation.extra B.pointer.grant .Write physical.offset (physical.offset+1))
    (sourceId : AllocId) (sourceTag : BorTag) (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (sourceLive : machine.memory.live.find? (fun row=>row.1==sourceId)=some (sourceId,sourceEntry))
    (sourceLeaf : CurrentCallEmptyEntrySourceData.Leaf sourceEntry.allocation.extra sourceTag)
    (sourceHiddenOnBool : ∀index current,B.allocation.extra.nodes.get index=some current→current.tag=sourceTag→current.isExposed=false)
    (root : RootFrame) (raw : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (adjusted : Immediate Provenance) (frame : CompilerFrameContext.ActualFrame)
    (installed : frame=PositiveRootInstalledFrame.installed root adjusted 0 {} sourceId sourceTag boolId node.tag)
    (rootStop : root.frame.returnContinuation=.stop true) (rootDestination : root.frame.returnPlace.toRuntimePlace=⟨.memory place.mplace,place.layout⟩)
    (rootVarargs : root.frame.vaList=#[])
    (model : DuplicatePrefixCallModel.Model options remaining span machine) (enabled : machine.borrowTracker=some tracker)
    (thread : Miri.Concurrency.ThreadRecord) (threadAt : machine.threads.activeThread?=some thread)
    (edge : B.precise.completion.parents[B.pointer.grant.toNat]?=some (some original.pointer.grant))
    (ready : CurrentCallBoolProtection.WindowReady machine physical.id physical.offset.toNat 1)
    (fuel : Nat) (fuelEq : options.limits.validation=fuel+1) :
    ∃final,SuccessfulTrace.Trace (config options (remaining+1) span) limits (Storage.withCurrent #[] frame machine) final ∧
      ExecutionMachine.step (config options (remaining+1) span) limits () final=(final,.ok false) ∧final.stack.frames=#[] := by
  obtain ⟨result,traceBefore,body,identity,callee,size,located,slot0,returnPlace,extra,continuation,varargs,immediate⟩ :=
    (CurrentCallBodyPrefix.body_prefix_of_installed options limits remaining span root raw adjusted 0 {} sourceId sourceTag boolId node.tag frame machine installed model fuel fuelEq).1 rfl
  let beforeReturn:=RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span machine)
  have memory : beforeReturn.memory=machine.memory := by
    unfold beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators] <;>rfl
  have addresses : beforeReturn.user.addresses=machine.user.addresses := by
    unfold beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators] <;>rfl
  have extras : beforeReturn.user.payload.payload.user.runtime.extras=machine.user.payload.payload.user.runtime.extras := by
    unfold beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators] <;>rfl
  have enabledNow : beforeReturn.borrowTracker=some tracker := by
    unfold beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact enabled
  have activeNow : beforeReturn.threads.activeThread?=some thread := by
    unfold beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact threadAt
  have present : Present (ActualWorld beforeReturn) boolId B.allocation := by
    unfold Present ActualWorld
    rw [memory]
    exact B.present
  let afterB : UniformWindow beforeReturn tracker data owner boolId boolOffset 1 .ret := {B with
    present:=present
    issued:=CurrentCallAllocationLicense.spatial B.issued beforeReturn tracker B.allocation present rfl rfl rfl rfl
      (by intro position root found;exact found) (by intro index current found;exact ⟨current,found,rfl,rfl,rfl,rfl⟩)
      B.precise.completion (by intro first second e;exact e)}
  obtain ⟨P,pointerEq,idEq,offsetEq,entryEq,bindingP⟩ := CurrentCallRootPhysicalWindow.view (final:=beforeReturn) physical binding addresses (congrArg MemoryState.live memory)
  have physId : P.id=boolId:=idEq.trans sameId
  have physOffset : P.offset.toNat=boolOffset:=(congrArg UInt64.toNat offsetEq).trans sameOffset
  have physAllocation : P.entry.allocation=afterB.allocation:=(congrArg LocalAllocation.allocation entryEq).trans sameAllocation
  have bLive : beforeReturn.memory.live.find? (fun row=>row.1==boolId)=some (boolId,P.entry) := by rw [←physId];exact P.live
  let borrowFrame:FrameState:=(({} : FrameState).addProtector sourceId sourceTag).addProtector boolId node.tag
  obtain ⟨sourceIndex,sourceNode,sourceTagged,sourcePresent,sourceNodeTag,sourceNodeLeaf,sourceHidden,inactive⟩ := sourceLeaf
  obtain ⟨released⟩ := CurrentCallResourceEmptyRootRelease.release afterB runtime distinct short concrete node nodeAt hidden sourceId sourceTag sourceEntry
    (by rw [memory];exact sourceLive) sourceIndex sourceNode sourceTagged sourcePresent sourceHidden
    (CurrentCallResourceEmptyRootRelease.quiescent_of_inactive _ _ _ inactive) sourceHiddenOnBool borrowFrame rfl original.pointer.grant edge
    P.offset physOffset (by rw [offsetEq];exact activeB) P.entry bLive physAllocation
  have parentNow : SpatialDelegation beforeReturn tracker boolId afterB.allocation afterB.precise.completion original.pointer.grant :=
    CurrentCallAllocationLicense.spatial parentIssued beforeReturn tracker B.allocation present rfl rfl rfl rfl
      (by intro position root found;exact found) (by intro index current found;exact ⟨current,found,rfl,rfl,rfl,rfl⟩)
      B.precise.completion (by intro first second e;exact e)
  have metadata:=PositiveRootInstalledFrame.metadata root adjusted 0 {} sourceId sourceTag boolId node.tag
  rw [←installed] at metadata
  have frameTracked : result.extra.borrowTracker=some borrowFrame := by rw [extra];exact metadata.2.2.2.2.2.2.2.1
  have noClocks : result.extra.dataRace=none := by rw [extra];exact metadata.2.2.2.2.2.2.1.trans root.noClocks
  have stop : result.returnContinuation=.stop true:=continuation.trans (metadata.2.2.2.1.trans rootStop)
  have destination : result.returnPlace.toRuntimePlace=⟨.memory place.mplace,place.layout⟩ := by rw [returnPlace,metadata.2.2.2.2.1];exact rootDestination
  have va : result.vaList=#[]:=varargs.trans (metadata.2.2.2.2.2.1.trans rootVarargs)
  have readyNow : CurrentCallBoolProtection.WindowReady beforeReturn P.id P.offset.toNat 1 := by rw [idEq,offsetEq];exact ready.transport extras
  obtain ⟨final,returned,terminal,emptyStack⟩ := CurrentCallResourceRootFinish.finish options limits remaining span place original afterB P bindingP physId physOffset
    (pointerEq.trans samePointer) parentNow parentBinding result borrowFrame released
    (tick_model options remaining span _ (tick_model options remaining span _ model)) enabledNow frameTracked thread activeNow
    body located size noClocks stop va immediate true slot0 destination readyNow fuel fuelEq
  exact ⟨final,SuccessfulTrace.append traceBefore returned,terminal,emptyStack⟩
end
end DuplicatePrefix.CurrentCallEmptyLiveZeroFinish
