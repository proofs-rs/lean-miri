import duplicate_prefix.GeneralBorrowPositiveWildcardAcceptedCallFlags
import duplicate_prefix.GeneralBorrowScopedCopyPhysicalOutput
import duplicate_prefix.GeneralBorrowScopedDualDataReturnPlan
import duplicate_prefix.GeneralBorrowScopedDualRootPhysicalExit
import duplicate_prefix.GeneralBorrowScopedFullDataFlags
import duplicate_prefix.CopyRootExitData
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardAcceptedExitInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Concurrency
open GeneralBorrowExposedScopedAsMutCallInput GeneralBorrowExposedScopedAsMutCallReturn
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 1000000
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
set_option autoImplicit false in
/-- Internal derived pipeline data. The original caller contract has none of
these post-copy fields: actual copy output and source-restored target data
construct this record before the final physical exit is formed. -/
structure PostCopy (s : GeneralBorrowPositiveWildcardAcceptedInput.Initial) where
  updated : Allocation Provenance BorrowTree
  call : GeneralBorrowExposedScopedAsMutToCopy.Input
  source : GeneralBorrowPositiveWildcardAcceptedCallSource.Facts s updated call
  root : CompilerFrameContext.ActualFrame
  post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser
  shape : PositiveRootSuccessProfile.FrameShape call.caller root
    (GeneralBorrowExposedScopedAsMutToCopy.scalar call) (GeneralBorrowExposedScopedAsMutToCopy.destinationScalar call) call.count
  memory : post.memory=RetagEntry.updatedMemory call.machine.memory call.id call.entry (released call.toInput)
  tracked : post.borrowTracker=some {held call.toInput with global:=(held call.toInput).global.endCall (({} : FrameState).addProtector call.id call.tracker.global.nextPointerTag)}
  runtime : GenericSharedLenAccepted.RuntimeFacts call.options call.remaining call.span call.machine post
  copy : CopyRootEntry.Input call.options call.limits call.remaining call.span #[] root post
    (GeneralBorrowExposedScopedAsMutToCopy.scalar call) (GeneralBorrowExposedScopedAsMutToCopy.destinationScalar call) call.count
  data : GeneralBorrowScopedCopyRootGuardBody.CopyData call.options call.remaining call.span post copy.tracker
    (GeneralBorrowExposedScopedAsMutToCopy.scalar call) (GeneralBorrowExposedScopedAsMutToCopy.destinationScalar call) call.count
  dataId : data.id=s.id
  output : GeneralBorrowScopedCopyPhysicalOutput.Output call.options call.limits call.remaining call.span #[] root post
    (GeneralBorrowExposedScopedAsMutToCopy.scalar call) (GeneralBorrowExposedScopedAsMutToCopy.destinationScalar call) call.count copy data
  target : UniIndex
  selected : UniIndex
  head : UniIndex
  tail : List UniIndex
  context : GeneralBorrowExposedKnownRootRangeData.Context output.result.extra target selected head tail
  tagged : output.result.extra.indexOfTag s.tracker.global.nextPointerTag=some target
  owned : ∀ kind,GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty (GeneralBorrowExposedKnownRootRangeData.Data
    output.result.extra location copy.tracker.global.protectedTags target selected head tail kind)) 0 s.len output.result.extra.locations
  fits : output.result.extra.nodes.data.size≤4294967296
  capacity : output.result.extra.locations.size.bytes=s.len

/-- Form the complete actual root buffer/bool-slot release and true-return
input. Slot liveness, its held/free bits, caller metadata and mixed callback
activity are all derived from the actual pipeline records. -/
def input (s : GeneralBorrowPositiveWildcardAcceptedInput.Initial) (p : PostCopy s) :
    GeneralBorrowScopedDualRootPhysicalExit.Input := by
  let slot : LocalAllocation Provenance BorrowTree MiriMemoryKind:={s.slotEntry with allocation:=p.updated}
  let slotTag:=(GeneralBorrowPositiveWildcardFunctionState.next s.tracker s.fresh).global.nextPointerTag
  have slotBefore : p.post.memory.live.find? (fun row=>row.1==s.slotId)=some (s.slotId,slot) := by
    rw [p.memory]
    exact StackPopRelease.lookup_commit_other p.call.machine.memory p.call.id s.slotId p.call.entry slot (released p.call.toInput)
      (by rw [p.source.id];exact s.separate) p.source.slotPresent
  have slotPresent : p.output.finalMachine.memory.live.find? (fun row=>row.1==s.slotId)=some (s.slotId,slot) := by
    rw [p.output.memory,CopyRootExitData.memory_after_eq_commit]
    exact StackPopRelease.lookup_commit_other p.post.memory p.data.id s.slotId ⟨p.data.kind,p.output.result⟩ slot p.output.result.extra
      (by rw [p.dataId];exact s.separate) slotBefore
  have trackerEq : p.copy.tracker={held p.call.toInput with global:=(held p.call.toInput).global.endCall (({} : FrameState).addProtector p.call.id p.call.tracker.global.nextPointerTag)} :=
    Option.some.inj (p.copy.tracked.symm.trans p.tracked)
  have tagsEq : p.copy.tracker.global.protectedTags=(GeneralBorrowPositiveWildcardAcceptedUnheld.mutableEnded s).protectedTags := by
    rw [trackerEq]
    exact GeneralBorrowPositiveWildcardAcceptedCallFlags.table s p.updated p.call p.source
  have flags:=GeneralBorrowPositiveWildcardAcceptedSlotFlags.after_mutable s
  have rootFree : p.copy.tracker.global.protectedTags.contains s.slotRoot=false := by rw [tagsEq];exact flags.1
  have slotHeld : p.copy.tracker.global.protectedTags.contains slotTag=true := by rw [tagsEq];exact flags.2
  let buffer : LocalAllocation Provenance BorrowTree MiriMemoryKind:=⟨p.data.kind,p.output.result⟩
  have bufferPresent : p.output.finalMachine.memory.live.find? (fun row=>row.1==s.id)=some (s.id,buffer) := by
    simpa only [p.dataId] using p.output.live
  have hidden : p.context.anchorNode.isExposed=false :=
    GeneralBorrowScopedFullDataFlags.hidden p.output.result.extra p.copy.tracker.global.protectedTags p.target p.selected p.head p.tail p.context .Read
      p.output.well (by rw [p.capacity];exact s.positive) (by rw [p.capacity];exact p.owned .Read)
  let release:=GeneralBorrowScopedDualDataReturnPlan.build p.output.finalMachine.memory p.copy.tracker.global.protectedTags
    s.id s.tracker.global.nextPointerTag buffer bufferPresent p.target p.selected p.head p.tail p.context hidden p.tagged s.len
    (UInt64.lt_iff_toNat_lt.mp s.positive) p.output.well p.capacity p.fits p.owned s.slotId s.separate slot slotPresent
    s.slotRoot slotTag p.source.slotTree rootFree slotHeld s.slotDistinct
  let thread:=Classical.choose p.output.active
  have active:=Classical.choose_spec p.output.active
  exact {
    options:=p.call.options,limits:=p.call.limits,remaining:=p.call.remaining,span:=p.call.span,source:=p.call.source,fuel:=p.call.fuel,
    debugOff:=p.call.debug,validationFuel:=p.call.validation,context:=s.writeContext,validationContext:=s.validationContext,
    accessEq:=p.source.accessEq,validationWidth:=s.validationWidth,validationRuntimeSize:=s.validationRuntimeSize,sameRuntime:=s.sameRuntime,
    width:=s.width,runtimeWidth:=s.runtimeWidth,runtimeSize:=s.runtimeSize,outerAccessEq:=p.source.outerAccessEq,
    before:=p.call.caller,ready:=CopyRootOutput.caller p.root p.copy.valid,
    pointer:=GeneralBorrowExposedScopedAsMutToCopy.scalar p.call,destinationValue:=GeneralBorrowExposedScopedAsMutToCopy.destinationScalar p.call,
    count:=p.call.count,shape:=CopyRootSuccessShape.of_copy _ _ _ _ _ p.shape p.source.local0 p.copy.valid,
    body:=p.call.body,identity:=p.call.identity,callee:=p.call.callee,noLocalClocks:=p.call.clocks,continuation:=p.source.continuation,varargs:=p.source.varargs,
    machine:=p.output.finalMachine,tracker:=p.copy.tracker,tracked:=p.output.tracked,
    defaultMode:=by rw [trackerEq];exact p.call.mode,
    noClocks:=p.output.race,noBackend:=p.output.backend.trans p.runtime.backend,
    ghost:=p.output.ghost,shallow:=p.output.shallow,unchecked:=p.output.unchecked,noGc:=p.output.noGc,fixed:=p.output.fixed,
    thread:=thread,active:=active,release:=release,frameTracked:=p.source.frameBorrow,
    slotSize:=p.source.slotSize,slotStorage:=p.source.slotLen,slotMask:=p.source.slotMask,slotProvenance:=p.source.slotProvenance,slotMutable:=p.source.slotMutable,
    place:=s.place,layout:=s.layout,slotBase:=s.slotBase,slotPointer:=s.slotPointer,aligned:=s.aligned,fits:=s.slotFits,
    cached:=by rw [p.output.addresses,p.runtime.addresses];exact p.source.slotCached,
    extras:=by change p.output.finalMachine.user.payload.payload.user.runtime.extras.allocations.find? _ = _
               rw [p.output.extras,p.runtime.extras];exact p.source.slotExtras,
    destination:=p.source.returnPlace }

theorem build (s : GeneralBorrowPositiveWildcardAcceptedInput.Initial) (p : PostCopy s) :
    ∃ exit : GeneralBorrowScopedDualRootPhysicalExit.Input,
      exit.options=s.options ∧ exit.limits=s.limits ∧ exit.remaining=s.remaining ∧ exit.span=s.span ∧
      GeneralBorrowScopedDualRootPhysicalExit.caller exit=CopyRootOutput.caller p.root p.copy.valid ∧
      exit.machine=p.output.finalMachine := by
  exact ⟨input s p,p.source.options,p.source.limits,p.source.remaining,p.source.span,rfl,rfl⟩
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardAcceptedExitInput
