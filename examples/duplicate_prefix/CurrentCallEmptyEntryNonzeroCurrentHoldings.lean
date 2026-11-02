import duplicate_prefix.CurrentCallEmptyEntryNonzeroDispatch
import duplicate_prefix.CurrentCallEmptyEntryLenZeroHoldings
import duplicate_prefix.S03EmptySharedGeometry
import duplicate_prefix.GeneralBorrowFreshGeometry

namespace DuplicatePrefix.CurrentCallEmptyEntryNonzeroCurrentHoldings
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Interpreter
open CandidateCurrentJointCall RootFrameData EmptyRootArguments TypedBorrowSteps ReferenceBorrowDriver
open CandidateStableCallOwnership CurrentCallEmptyEntryNonzeroDispatchState CurrentCallEmptyEntryNonzeroDispatch
open CurrentCallEmptyEntryBool
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section
variable {options limits remaining span before tracker argument place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data}

/-- The exact final tree retained by the actual live body branch. -/
def after {out : CurrentCallEmptyEntryRoot.Output input #[]} {count : UInt64} {post : Before}
    (heap : LiveHeap out count post) : BorrowTree :=
  (S03EmptyNextLenInput.form heap.entry.allocation.extra (held out).global heap.runtime
    tracker.global.nextPointerTag heap.first heap.fresh heap.room).after

private theorem runtime_advance (tree : BorrowTree) (before after : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree before)
    (same : after.protectedTags=before.protectedTags)
    (raise : before.nextPointerTag.value.toNat≤after.nextPointerTag.value.toNat) :
    DuplicatePrefixBorrowContract.RuntimeFacts tree after := by
  refine ⟨?_,?_,runtime.possible,?_⟩
  · simpa only [same] using runtime.formed
  · simpa only [same] using runtime.coherent
  · rw [same]
    exact GeneralBorrowForestTagHighWaterHistory.weaken tree before.protectedTags before.nextPointerTag after.nextPointerTag runtime.below raise

private theorem initial_live (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64) : (machine out count).memory.live.find? (fun row=>row.1==out.physical.id)=
      some (out.physical.id,{out.physical.entry with allocation:=out.updated}) := by
    change (((ReturnProtection.borrowedState #[] (atSpan (RootArgumentsTwo.result out.firstDone count) ⟨601⟩).frame
      (CurrentCallEmptyEntryRoot.sourceBorrow out.effect {}) (sourceMachine out) (sourceTracker out) out.room
      out.physical.id out.physical.entry out.certificate.output.child.tree).machine.memory.live.filter
      fun row=>row.1!=out.physical.id).push (out.physical.id,{out.physical.entry with allocation:=out.updated})).find?
      (fun row=>row.1==out.physical.id)=_
    exact MemoryCopyBridge.live_lookup_replaced _ out.physical.id _

/-- SAME-allocation body holdings are derived from the actual entry and two
helper trees, under the actual post-body tracker and its unchanged held table. -/
private theorem same_allocation_base (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64)
    (facts : CurrentCallEmptyEntryRoot.Facts out count)
    (result : CompilerFrameContext.ActualFrame) (post : Before) (body : BodyResult out count result post)
    (heap : LiveHeap out count post) (sameId : heap.id=out.physical.id) :
    ∃ current,post.borrowTracker=some current ∧
      Nonempty (BoolHoldings (after heap) current.global out.certificate.output.tag tracker.global.nextPointerTag
        out.physical.pointer.provenance (UInt64.ofNat call.returnOffset)) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts (after heap) current.global ∧
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder (after heap) := by
  obtain ⟨current,tracked,mode,globalEq,flags,counter⟩ := body.tracked
  have initialLive := initial_live out count
  have entryEq : heap.entry={out.physical.entry with allocation:=out.updated} := by
    have live := heap.live
    rw [sameId,initialLive] at live
    exact (Prod.mk.inj (Option.some.inj live)).2.symm
  have extra : out.updated.extra=(CurrentCallEmptyEntryCompleteRelease.written out.certificate.output (UInt64.ofNat call.returnOffset)).tree :=
    facts.2.2.2.2.2.2.1
  obtain ⟨initialHoldings⟩ := out.certificate.holdings
  have initial : Nonempty (BoolHoldings heap.entry.allocation.extra (held out).global out.certificate.output.tag tracker.global.nextPointerTag
      out.physical.pointer.provenance (UInt64.ofNat call.returnOffset)) := by
    rw [entryEq]
    change Nonempty (BoolHoldings out.updated.extra out.certificate.output.global _ _ _ _)
    rw [extra]
    exact ⟨initialHoldings⟩
  obtain ⟨initialHoldings⟩ := initial
  obtain ⟨holdings⟩ := CurrentCallEmptyEntryLenZeroHoldings.global _ (held out).global current.global _ _ _ _ initialHoldings flags
  have currentRuntime := runtime_advance _ (held out).global current.global heap.runtime flags (by omega)
  let second := S03EmptyNextLenInput.form heap.entry.allocation.extra (held out).global heap.runtime
    tracker.global.nextPointerTag heap.first heap.fresh heap.room
  have secondParent : second.parent=heap.first.index := by
    rfl
  have growth : EmptyForestSharedPoolNext.growth heap.first≤1 := by
    unfold EmptyForestSharedPoolNext.growth
    split <;> omega
  have size := EmptyForestSharedPoolNext.node_size heap.first
  have room1 : heap.entry.allocation.extra.nodes.size+1≤4294967295 := by have room:=heap.room;omega
  have room2 : heap.first.after.nodes.size+1≤4294967295 := by have room:=heap.room;omega
  have successor := GenericFunctionEntryNumerics.successor_value (held out).global.nextPointerTag heap.fresh
  have bound1 : (held out).global.nextPointerTag.value.toNat<current.global.nextPointerTag.value.toNat := by omega
  have bound2 : (TypedRetagEmpty.successorTag (held out).global.nextPointerTag heap.fresh).value.toNat<current.global.nextPointerTag.value.toNat := by omega
  have different : out.certificate.output.tag≠tracker.global.nextPointerTag := by
    have sourceCounter := source_counter out
    have firstValue := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag (fresh input)
    have actualTag := out.certificate.tag
    change out.certificate.output.tag=(sourceTracker out).global.nextPointerTag at actualTag
    intro same
    rw [actualTag,sourceCounter] at same
    have values := congrArg (fun tag : BorTag=>tag.value.toNat) same
    omega
  have qLeaf : CurrentCallEmptyEntrySourceData.Leaf heap.entry.allocation.extra tracker.global.nextPointerTag := by
    rw [entryEq]
    change CurrentCallEmptyEntrySourceData.Leaf out.updated.extra _
    rw [extra]
    exact out.certificate.qLeaf (heap.allocation.trans (congrArg some sameId))
  obtain ⟨finalHoldings⟩ := CurrentCallEmptyEntryLenZeroHoldings.two_helpers _ current.global _ _ _ _ holdings currentRuntime
    (held out).global.nextPointerTag (TypedRetagEmpty.successorTag (held out).global.nextPointerTag heap.fresh)
    heap.first second secondParent room1 room2 bound1 bound2 different qLeaf
  have runtime1 := S03EmptySharedRuntime.construct _ current.global currentRuntime _ _ heap.first room1 bound1
  have runtime2 := S03EmptySharedRuntime.construct _ current.global runtime1 _ _ second room2 bound2
  have ordered : GeneralBorrowWildcardParentTagOrder.ParentTagOrder heap.entry.allocation.extra := by
    rw [entryEq]
    change GeneralBorrowWildcardParentTagOrder.ParentTagOrder out.updated.extra
    rw [extra]
    exact out.certificate.order
  have order1 := S03EmptySharedGeometry.fresh_order _ (held out).global heap.runtime _ heap.first ordered
  obtain ⟨child,childAt,childTag,_,_,_,_⟩ := GeneralBorrowFreshMetadataChildSifa.node_fields heap.first.stage heap.first.parent .Read
    heap.first.index (GeneralBorrowFreshAnchor.sharedNode (held out).global.nextPointerTag heap.first.parent) heap.first.stage_new
  have parentAt : heap.first.after.nodeAt heap.first.index=some second.parentNode := by simpa only [secondParent] using second.present
  have childEq : child=second.parentNode := Option.some.inj (childAt.symm.trans parentAt)
  have parentTag : second.parentNode.tag=(held out).global.nextPointerTag := childEq ▸ childTag
  have order2 := S03EmptySharedGeometry.order second order1 (by rw [parentTag];apply UInt64.le_iff_toNat_le.mpr;omega)
  exact ⟨current,tracked,⟨finalHoldings⟩,runtime2,order2⟩

private theorem shared_frame {tree : BorrowTree} {parentTag tag : BorTag}
    (step : EmptyForestSharedPool.Input tree parentTag tag) (well : tree.locations.WellFormed) :
    step.after.locations.WellFormed ∧ step.after.locations.size=tree.locations.size :=
  GeneralBorrowFreshGeometry.sifa_frame step.stage step.parent .Read well

private theorem short_bound (initial written middle final growth1 growth2 : Nat)
    (margin : initial+8<65536) (writtenGrowth : written≤initial+1)
    (firstSize : middle=written+growth1) (firstGrowth : growth1≤1)
    (secondSize : final=middle+growth2) (secondGrowth : growth2≤1) : final<65536 := by omega

private theorem bounds_short (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64)
    (facts : CurrentCallEmptyEntryRoot.Facts out count) (post : Before)
    (heap : LiveHeap out count post) (sameId : heap.id=out.physical.id) :
    (UInt64.ofNat call.returnOffset).toNat+1≤(after heap).locations.size.bytes.toNat ∧ (after heap).nodes.size<65536 := by
  have entryEq : heap.entry={out.physical.entry with allocation:=out.updated} := by
    have live := heap.live
    rw [sameId,initial_live out count] at live
    exact (Prod.mk.inj (Option.some.inj live)).2.symm
  have extra : out.updated.extra=(CurrentCallEmptyEntryCompleteRelease.written out.certificate.output (UInt64.ofNat call.returnOffset)).tree :=
    facts.2.2.2.2.2.2.1
  let second := S03EmptyNextLenInput.form heap.entry.allocation.extra (held out).global heap.runtime
    tracker.global.nextPointerTag heap.first heap.fresh heap.room
  have frame1 := shared_frame heap.first heap.runtime.formed.well
  have frame2 := shared_frame second frame1.1
  have capacity1 : heap.first.after.locations.size=heap.entry.allocation.extra.locations.size := frame1.2
  have capacity2 : second.after.locations.size=heap.first.after.locations.size := frame2.2
  have bounds : (UInt64.ofNat call.returnOffset).toNat+1≤second.after.locations.size.bytes.toNat := by
    rw [capacity2,capacity1,entryEq]
    change (UInt64.ofNat call.returnOffset).toNat+1≤out.updated.extra.locations.size.bytes.toNat
    rw [extra]
    exact out.certificate.bounds
  have staged := CurrentCallEmptyEntryNonzeroDispatchRuntime.stage (CurrentCallPush.prepared_input input #[]) out.effect #[]
    (EmptyRootArguments.firstLive (root input)).frame {} 1 ((EmptyRootArguments.firstLive (root input)).valid EmptyRootArguments.i1) heap.id heap.allocation
  change (∃ metadataTag,DuplicatePrefixEmptyReferenceInput.Metadata (sourceMachine out).memory heap.id metadataTag ∧
      (sourceMachine out).memory.live.find? (fun row=>row.1==heap.id)=none) ∨
    ∃ entry,(sourceMachine out).memory.live.find? (fun row=>row.1==heap.id)=some (heap.id,entry) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra (sourceTracker out).global ∧ entry.allocation.extra.nodes.size+8<65536 at staged
  have physicalLive : (sourceMachine out).memory.live.find? (fun row=>row.1==out.physical.id)=some (out.physical.id,out.physical.entry) := out.physical.live
  have oldMargin : out.physical.entry.allocation.extra.nodes.size+8<65536 := by
    rcases staged with ⟨metadataTag,metadata,absent⟩ | ⟨old,live,_,margin⟩
    · rw [sameId,physicalLive] at absent
      cases absent
    · rw [sameId,physicalLive] at live
      have equal : old=out.physical.entry := (Prod.mk.inj (Option.some.inj live)).2.symm
      exact equal ▸ margin
  have boolGrowth := out.certificate.growth
  rw [←extra] at boolGrowth
  have growth1 : EmptyForestSharedPoolNext.growth heap.first≤1 := by
    unfold EmptyForestSharedPoolNext.growth
    split <;> omega
  have growth2 : EmptyForestSharedPoolNext.growth second≤1 := by
    unfold EmptyForestSharedPoolNext.growth
    split <;> omega
  have size1 := EmptyForestSharedPoolNext.node_size heap.first
  have size2 := EmptyForestSharedPoolNext.node_size second
  have entrySize : heap.entry.allocation.extra.nodes.size=out.updated.extra.nodes.size := by rw [entryEq]
  have writtenMargin : heap.entry.allocation.extra.nodes.size≤out.physical.entry.allocation.extra.nodes.size+1 := by rw [entrySize];exact boolGrowth
  exact ⟨bounds,short_bound _ _ _ _ _ _ oldMargin writtenMargin size1 growth1 size2 growth2⟩

/-- Derive current holdings and all physical release bounds from the SAME
actual two-helper body output, without an additional caller premise. -/
theorem same_allocation (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64)
    (facts : CurrentCallEmptyEntryRoot.Facts out count)
    (result : CompilerFrameContext.ActualFrame) (post : Before) (body : BodyResult out count result post)
    (heap : LiveHeap out count post) (sameId : heap.id=out.physical.id) :
    ∃ current,post.borrowTracker=some current ∧
      Nonempty (BoolHoldings (after heap) current.global out.certificate.output.tag tracker.global.nextPointerTag
        out.physical.pointer.provenance (UInt64.ofNat call.returnOffset)) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts (after heap) current.global ∧
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder (after heap) ∧
      (UInt64.ofNat call.returnOffset).toNat+1≤(after heap).locations.size.bytes.toNat ∧
      (after heap).nodes.size<65536 := by
  obtain ⟨current,tracked,holdings,runtime,order⟩ := same_allocation_base out count facts result post body heap sameId
  obtain ⟨bounds,short⟩ := bounds_short out count facts post heap sameId
  exact ⟨current,tracked,holdings,runtime,order,bounds,short⟩

end
end DuplicatePrefix.CurrentCallEmptyEntryNonzeroCurrentHoldings
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryNonzeroCurrentHoldings" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual nonzero holdings dependency {dependency}"
