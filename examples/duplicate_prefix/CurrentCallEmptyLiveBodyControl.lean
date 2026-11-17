import duplicate_prefix.S03EmptyPositiveBodyExact
import duplicate_prefix.CurrentCallEmptyLiveFrames
import duplicate_prefix.DuplicatePrefixTypeCacheOrigins
namespace DuplicatePrefix.CurrentCallEmptyLiveBodyControl
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext RootFrameData
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Actual zero Shared allocator data from current source metadata alone.
No source byte permission, content family or positive window is involved. -/
def sourceInput (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag : BorTag) (parent : UniIndex) (node : TreeNode)
    (tagged : tree.indexOfTag parentTag=some parent) (present : tree.nodeAt parent=some node)
    (room : tree.nodes.size+2≤4294967295) : EmptyForestSharedPool.Input tree parentTag global.nextPointerTag := by
  let depth:=Classical.choice runtime.formed.depth
  apply EmptyForestSharedPool.factory tree parentTag global.nextPointerTag parent node depth tagged present
    (ConcreteEmptyRuntimeEntry.counter_fresh tree global runtime.below) runtime.formed.allocator.pool runtime.formed.allocator.accounting
  · have accounting:=runtime.formed.allocator.accounting
    unfold GeneralBorrowFreshStagePool.Accounting at accounting
    omega
  · exact DuplicatePrefixBorrowContract.vacant_clean runtime

/-- The SAME actual concrete-q empty value (also produced by a wildcard
source retag) executes Shared, the zero Len helper and the rejecting branch. -/
theorem to_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (root : RootFrame) (raw : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (machine : Before) (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker)
    (model : DuplicatePrefixCallModel.Model options remaining span machine)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins machine.user.payload.payload.user.types)
    (parentTag : BorTag) (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (parent : UniIndex) (parentNode : TreeNode)
    (tagged : entry.allocation.extra.indexOfTag parentTag=some parent) (nodeAt : entry.allocation.extra.nodeAt parent=some parentNode)
    (borrowRuntime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (base offset count : UInt64) (nonzero : base+offset≠0) (countNonzero : count≠0)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row=>row.1==id)=some (id,entry))
    (boolId : AllocId) (boolTag : BorTag) (frame : CompilerFrameContext.ActualFrame)
    (installed : frame=PositiveRootInstalledFrame.installed root
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
      count {} id parentTag boolId boolTag)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (tagRoomNext : tracker.global.nextPointerTag.value.toNat+1<18446744073709551615)
    (nodeRoomTwo : entry.allocation.extra.nodes.size+2≤4294967295)
    (dynamicFuel validityFuel budget : Nat)
    (dynamicEq : options.place.dynamicFuel=dynamicFuel+1) (validityEq : options.limits.validation=validityFuel+1)
    (dispatchFuel : limits.callDispatch=budget+1)
    (thread : Miri.Concurrency.ThreadRecord) (activeThread : machine.threads.activeThread?=some thread)
    (topZero : thread.topUserRelevantFrame=some 0) :
    let input:=sourceInput entry.allocation.extra tracker.global borrowRuntime parentTag parent parentNode tagged nodeAt nodeRoomTwo
    ∃ result : CompilerFrameContext.ActualFrame,
      ∃ finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      ∃ finalTree : BorrowTree, ∃ finalTracker : MachineHooks.BorrowState,
      finalTree = (S03EmptyNextLenInput.form entry.allocation.extra tracker.global borrowRuntime parentTag
        input fresh nodeRoomTwo).after ∧
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent #[] frame machine) (Storage.withCurrent #[] result finalMachine) ∧
      result.body = frame.body ∧ result.bodyIdentity = frame.bodyIdentity ∧ result.functionInstance = frame.functionInstance ∧
      result.extra = frame.extra ∧ result.returnPlace = frame.returnPlace ∧ result.returnContinuation = frame.returnContinuation ∧
      result.vaList = frame.vaList ∧ result.localsIdentity = frame.localsIdentity ∧ result.locals.size = 25 ∧
      result.location = .mir ⟨10,0⟩ ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      CopyHelperCleanup.AllImmediate result ∧
      finalMachine.memory.live.find? (fun row => row.1 == id) = some (id,{entry with allocation := entry.allocation.setExtra finalTree}) ∧
      finalMachine.memory = RetagEntry.updatedMemory machine.memory id entry finalTree ∧
      finalMachine.borrowTracker = some finalTracker ∧ finalTracker.retagMode = tracker.retagMode ∧
      (∃ nextFresh : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag.value < 18446744073709551615,
        finalTracker = PositiveLenPost.trackerAfter (ReferenceBorrowDriver.allocatedTracker tracker fresh) nextFresh id) ∧
      finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      finalMachine.dataRace = none ∧ finalMachine.threads.fixedScheduling = true ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).gcInterval = 0 ∧
      finalMachine.user.addresses = machine.user.addresses ∧
      finalMachine.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      finalMachine.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      finalMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      (∃ finalThread, finalMachine.threads.activeThread? = some finalThread) := by
  dsimp only
  let input:=sourceInput entry.allocation.extra tracker.global borrowRuntime parentTag parent parentNode tagged nodeAt nodeRoomTwo
  let adjusted:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
  have size : frame.locals.size=25 := by rw [installed];exact PositiveRootInstalledFrame.size _ _ _ _ _ _ _ _
  have cells (index : Fin 25) := PositiveRootInstalledFrame.slot_option root raw adjusted count {} id parentTag boolId boolTag index
  rw [←installed] at cells
  have get (index : Fin 25) := Option.some.inj ((Array.getElem?_eq_getElem (show index.val<frame.locals.size by rw [size];exact index.isLt)).symm.trans (cells index))
  have all : CopyHelperCleanup.AllImmediate frame := by rw [installed];exact PositiveRootInstalledFrame.immediate _ raw _ _ _ _ _ _ _
  obtain ⟨body,identity,callee,_,_,_,clocks,_,location⟩:=PositiveRootInstalledFrame.metadata root adjusted count {} id parentTag boolId boolTag
  rw [←installed] at body identity callee clocks location
  obtain ⟨current,enabled,mode⟩:=model.defaultTracker
  have same : current=tracker:=Option.some.inj (enabled.symm.trans tracked)
  subst current
  have unused : ∀ index (valid:index<frame.locals.size),7≤index→index≤12→frame.locals[index]'valid=⟨.dead,none⟩ := by
    intro index valid lower upper
    have row:=get ⟨index,by omega⟩
    simpa only [show ¬(14=index ∨13=index ∨6=index ∨0=index) by omega,show ¬2=index by omega,show ¬1=index by omega,ite_false] using row
  have targetEq : (config options remaining span).access.runtime.base=(config options (remaining+1) span).access.runtime.base := by
    rw [actual_access_runtime options () remaining span,actual_access_runtime options () (remaining+1) span]
  exact S03EmptyPositiveBodyExact.to_return options limits remaining span (DuplicatePrefixCallModel.sourceComparator options remaining span machine model)
    model.nullComparator model.preciseOff model.implicitOff model.debugOff dynamicFuel validityFuel dynamicEq validityEq frame machine parentTag tracker.global.nextPointerTag
    id entry base offset count nonzero countNonzero input size
    (by simpa [adjusted,targetEq] using congrArg LocalState.value (get ⟨1,by decide⟩))
    (by simpa using congrArg LocalState.layout (get ⟨1,by decide⟩))
    (by simpa using congrArg LocalState.value (get ⟨2,by decide⟩))
    (by simpa using congrArg LocalState.layout (get ⟨2,by decide⟩))
    (by simpa using congrArg LocalState.value (get ⟨3,by decide⟩))
    (by simpa using congrArg LocalState.layout (get ⟨3,by decide⟩))
    (by simpa using congrArg LocalState.value (get ⟨4,by decide⟩))
    (by simpa using congrArg LocalState.value (get ⟨5,by decide⟩))
    (by simpa using congrArg LocalState.layout (get ⟨4,by decide⟩))
    (by simpa using congrArg LocalState.layout (get ⟨5,by decide⟩)) unused
    (body.trans root.body) (identity.trans root.identity) (callee.trans root.callee) location (clocks.trans root.noClocks) all tracker tracked mode rfl fresh cachedAddress present
    model.ghostOff model.shallow model.unchecked model.noGc model.fixedScheduler model.metadata
    (DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ model.metadata origins) borrowRuntime budget dispatchFuel tagRoomNext nodeRoomTwo model.noDataRace model.noBackend thread activeThread topZero
    (by simpa using congrArg LocalState.value (get ⟨0,by decide⟩))
    (by simpa using congrArg LocalState.layout (get ⟨0,by decide⟩))
    (by simpa using congrArg LocalState.value (get ⟨13,by decide⟩))
    (by simpa using congrArg LocalState.layout (get ⟨13,by decide⟩))
end
end DuplicatePrefix.CurrentCallEmptyLiveBodyControl
