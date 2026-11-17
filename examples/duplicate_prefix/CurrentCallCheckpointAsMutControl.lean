import duplicate_prefix.CurrentCallCheckpointDefaultControl
import duplicate_prefix.CurrentCallCheckpointAsMutExecution
import duplicate_prefix.CurrentCallCheckpointMutable
namespace DuplicatePrefix.CurrentCallCheckpointAsMutControl
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows CandidateStableCallOwnership CandidateCurrentJointCall
open CurrentCallPostEntryCheckpoint CurrentCallCheckpointRoot3 CurrentCallSpatialCover CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
variable {options remaining span len count place limits}
  {checkpoint : Checkpoint options remaining span len count place} (out : Output checkpoint limits)
  (done : CurrentCallCheckpointDefaultControl.Done out)

def entry : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
  {CurrentCallCheckpointDefaultControl.entry out with allocation:=
    (CurrentCallCheckpointDefaultControl.entry out).allocation.setExtra (CurrentCallCheckpointDefaultControl.tree out)}

theorem valid15 : (15:MIR.LocalId)<done.frame.locals.size:=by rw [done.size];decide

abbrev Helper := CurrentCallCheckpointAsMutExecution.Helper options limits remaining span
  (CurrentCallCheckpointDefaultControl.machine out) (CurrentCallCheckpointDefaultControl.tracker out)
  out.source.role.backing.id (UInt64.ofNat checkpoint.offset) len (entry out) done.frame done.base
  out.tracker.global.nextPointerTag (CurrentCallCheckpointDefaultControl.fresh out) (valid15 out done)

private theorem fetched {frame : CompilerFrameContext.ActualFrame} {index : Nat} {slot : LocalState Provenance LocalLayout}
    (valid : index<frame.locals.size) (eq : frame.locals[index]?=some slot) : frame.locals[index]=slot :=
  Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans eq)

private theorem capacity_setExtra (allocation : Allocation Provenance BorrowTree) (tree : BorrowTree)
    (capacity : tree.locations.size=allocation.byteSize) :
    (allocation.setExtra tree).extra.locations.size=(allocation.setExtra tree).byteSize:=capacity

private theorem bounds_setExtra (allocation : Allocation Provenance BorrowTree) (tree : BorrowTree)
    (amount : Nat) (bound : amount≤allocation.byteSize.bytes.toNat) :
    amount≤(allocation.setExtra tree).byteSize.bytes.toNat:=bound

/-- The existing typed AsMut execution consumes certificates for the one
registered Read and Strong constructor selected by the spatial producer. -/
theorem of_steps
    (readDone : ((entry out).allocation.extra.performBorrowAccessRange (.concrete out.tracker.global.nextPointerTag)
      (Size.ofBytes (UInt64.ofNat checkpoint.offset)) (Size.ofBytes len) .Read
      (TypedBorrowSteps.registeredGlobal (CurrentCallCheckpointDefaultControl.tracker out)
        (CurrentCallCheckpointDefaultControl.tracker out).global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).status=.Completed)
    (childDone : (((entry out).allocation.extra.performBorrowAccessRange (.concrete out.tracker.global.nextPointerTag)
      (Size.ofBytes (UInt64.ofNat checkpoint.offset)) (Size.ofBytes len) .Read
      (TypedBorrowSteps.registeredGlobal (CurrentCallCheckpointDefaultControl.tracker out)
        (CurrentCallCheckpointDefaultControl.tracker out).global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).tree.newChild
      (Size.ofBytes (UInt64.ofNat checkpoint.offset)) (.concrete out.tracker.global.nextPointerTag)
      (CurrentCallCheckpointDefaultControl.tracker out).global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).outcome=.ok ())
    (budget : Nat) (dispatch : limits.callDispatch=budget+1) : Nonempty (Helper out done) := by
  have model:=CurrentCallCheckpointDefaultControl.model out
  have valid16 : (16:MIR.LocalId)<done.frame.locals.size:=by rw [done.size];decide
  have slot15:=fetched (valid15 out done) done.slot15
  have slot16:=fetched valid16 done.slot16
  have startEq : (UInt64.ofNat checkpoint.offset).toNat=checkpoint.offset:=by
    obtain ⟨a,b,c,d,e,f,g,h,i,j⟩:=out.source.binding
    have small:=out.source.role.family.value.offset.bytes.toNat_lt
    exact Nat.mod_eq_of_lt (by omega)
  have positive : (0:UInt64)<len:=UInt64.lt_iff_toNat_lt.mpr checkpoint.source.positive
  have nonzero : len≠0:=by
    intro zero
    have eq:=congrArg UInt64.toNat zero
    have p:=checkpoint.source.positive
    simp only [UInt64.toNat_zero] at eq
    omega
  have initialBounds : checkpoint.offset+len.toNat≤out.source.role.backing.allocation.extra.locations.size.bytes.toNat:=by
    let byte := (out.source.role.backing.id,checkpoint.offset+len.toNat-1)
    have hit : Window out.source.role.backing.id checkpoint.offset len.toNat byte:=⟨rfl,by dsimp only [byte];have p:=checkpoint.source.positive;omega,by dsimp only [byte];have p:=checkpoint.source.positive;omega⟩
    obtain ⟨i,inside⟩:=out.source.role.covered byte hit
    have bound:=((out.source.role.roles i ⟨byte,hit,inside⟩).available byte hit inside).1
    have cap:=(out.source.role.roles i ⟨byte,hit,inside⟩).issued.capability
    rw [cap.treeExtent,←cap.extent]
    dsimp only [byte] at bound
    omega
  have short : out.source.role.backing.allocation.extra.nodes.size<65536:=by have n:=out.source.nodes;omega
  have nodeRoom : out.source.role.backing.allocation.extra.nodes.size+1≤4294967295:=by have n:=out.source.nodes;omega
  obtain ⟨parent,node,mapped,present,tag,_,_,runtime,capacity,growth,rest⟩:=
    CurrentCallSpatialDefaultMutable.construct out.source.role out.source.runtime out.source.distinct short nodeRoom
      checkpoint.source.tag out.source.concrete (CurrentCallCheckpointDefaultControl.room out) (UInt64.ofNat checkpoint.offset) len startEq rfl nonzero
      (by rw [startEq];exact initialBounds)
  have allocationEq : out.source.role.backing.allocation=(CurrentCallCheckpointDefaultControl.entry out).allocation:=out.source.allocation
  have currentCapacity : (entry out).allocation.extra.locations.size=(entry out).allocation.byteSize:=by
    have oldCapacity : out.source.role.backing.allocation.extra.locations.size=out.source.role.backing.allocation.byteSize:=by
      let byte := (out.source.role.backing.id,checkpoint.offset)
      have hit : Window out.source.role.backing.id checkpoint.offset len.toNat byte:=⟨rfl,by simp [byte],by dsimp only [byte];have p:=checkpoint.source.positive;omega⟩
      obtain ⟨i,inside⟩:=out.source.role.covered byte hit
      exact (out.source.role.roles i ⟨byte,hit,inside⟩).issued.capability.treeExtent
    rw [allocationEq] at capacity oldCapacity
    have inferred := capacity.trans oldCapacity
    have cap : (CurrentCallCheckpointDefaultControl.tree out).locations.size=
        (CurrentCallCheckpointDefaultControl.entry out).allocation.byteSize:=by
      simpa only [CurrentCallCheckpointDefaultControl.tree,CurrentCallSpatialDefaultMutable.child,CurrentCallCheckpointRoot3.Output.tracker] using inferred
    exact capacity_setExtra (CurrentCallCheckpointDefaultControl.entry out).allocation (CurrentCallCheckpointDefaultControl.tree out) cap
  have physicalBounds : (UInt64.ofNat checkpoint.offset).toNat+len.toNat≤(entry out).allocation.byteSize.bytes.toNat:=by
    rw [startEq]
    obtain ⟨i,inside⟩:=out.source.role.covered (out.source.role.backing.id,checkpoint.offset)
      ⟨rfl,by omega,by have p:=checkpoint.source.positive;omega⟩
    have cap:=(out.source.role.roles i ⟨_,⟨rfl,by omega,by have p:=checkpoint.source.positive;omega⟩,inside⟩).issued.capability
    rw [cap.treeExtent,allocationEq] at initialBounds
    exact bounds_setExtra (CurrentCallCheckpointDefaultControl.entry out).allocation
      (CurrentCallCheckpointDefaultControl.tree out) (checkpoint.offset+len.toNat) initialBounds
  obtain ⟨thread,active,topZero⟩:=CurrentCallCheckpointDefaultControl.active out
  let caller:=AsMutUncachedCall.cachedCaller done.frame (valid15 out done)
  let next:=AsMutPtrReturn.accountedMachine options remaining span (CurrentCallCheckpointDefaultControl.machine out)
  let destination:=(LocalPlaces.localRuntimePlace 0 caller 15 CopyCompilerFacts.destPointerLayout).stackView
  let pushed:=AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent #[] caller next) destination
  have pushedSize : pushed.stack.frames.size=2:=rfl
  obtain ⟨index,current,top,topPresent⟩:=RelevanceCurrent.exists_current pushed.stack.frames thread
    (by rw [pushedSize];decide) (by
      intro index cached
      have same : index=0:=Option.some.inj (cached.symm.trans topZero)
      rw [same,pushedSize]
      decide)
  obtain ⟨ctx⟩:=ActualReferenceContext.exists_context options remaining span model.preciseOff model.implicitOff
  exact CurrentCallCheckpointAsMutExecution.helper options limits remaining budget dispatch span ctx model.debugOff model.nullComparator
    checkpoint.dynamicFuel checkpoint.validationFuel checkpoint.dynamicEq checkpoint.validationEq
    out.source.role.backing.id (entry out) done.base (UInt64.ofNat checkpoint.offset) len out.tracker.global.nextPointerTag
    positive done.nonnull checkpoint.source.signedFits physicalBounds done.frame (CurrentCallCheckpointDefaultControl.machine out)
    (CurrentCallCheckpointDefaultControl.tracker out) (CurrentCallCheckpointDefaultControl.tracked out) (CurrentCallCheckpointDefaultControl.mode out)
    (CurrentCallCheckpointDefaultControl.fresh out) readDone childDone currentCapacity (valid15 out done)
    (congrArg LocalState.value slot15) (congrArg LocalState.layout slot15) done.clocks model.ghostOff model.shallow
    done.cached (CurrentCallCheckpointDefaultControl.live out) model.noDataRace model.metadata (CurrentCallCheckpointDefaultControl.origins out)
    thread index current active top topPresent (DuplicatePrefixCallModel.sourceComparator options remaining span _ model)
    done.body done.identity done.callee done.location valid16 (congrArg LocalState.value slot16) (congrArg LocalState.layout slot16)
    model.noBackend model.unchecked model.noGc model.fixedScheduler

private theorem extra_setExtra (allocation : Allocation Provenance BorrowTree) (tree : BorrowTree) :
    (allocation.setExtra tree).extra=tree:=by cases allocation;rfl

theorem p_tree : CurrentCallCheckpointMutable.tree checkpoint out.result out.source=CurrentCallCheckpointDefaultControl.tree out := by
  unfold CurrentCallCheckpointMutable.tree CurrentCallSpatialDefaultMutableInstall.tree
  rw [out.source.allocation]
  rfl

theorem p_global : (CurrentCallCheckpointMutable.next checkpoint out.result out.source).global=
    (CurrentCallCheckpointDefaultControl.tracker out).global:=rfl

theorem s_actual : CandidateCurrentFnEntryRaw.operation (entry out).allocation.extra
    (CurrentCallCheckpointDefaultControl.tracker out).global {} out.source.role.backing.id
    (.concrete out.source.role.backing.id out.tracker.global.nextPointerTag) (UInt64.ofNat checkpoint.offset) len=
      .ok (CurrentCallCheckpointMutable.sOutput checkpoint out.result out.source):=by
  have actual:=CurrentCallCheckpointMutable.s_actual checkpoint out.result out.source
  rw [p_tree out,p_global out] at actual
  have extra : (entry out).allocation.extra=CurrentCallCheckpointDefaultControl.tree out:=
    extra_setExtra _ _
  rw [extra]
  exact actual

theorem output_eq : CurrentCallCheckpointMutable.sOutput checkpoint out.result out.source=
    CurrentCallTypedFnEntry.literal (entry out).allocation.extra (CurrentCallCheckpointDefaultControl.tracker out).global {}
      out.source.role.backing.id (CurrentCallCheckpointDefaultControl.fresh out)
      (.concrete out.source.role.backing.id out.tracker.global.nextPointerTag) (UInt64.ofNat checkpoint.offset) len:=by
  exact Except.ok.inj ((s_actual out).symm.trans (CurrentCallTypedFnEntry.literal_operation _ _ _ _ _ _ _ _))

private theorem literal_status (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (id : AllocId)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615) (parent : BorTag) (start amount : UInt64)
    (read : (CurrentCallTypedFnEntry.literal tree tracker.global {} id fresh (.concrete id parent) start amount).access.status=.Completed)
    (child : (CurrentCallTypedFnEntry.literal tree tracker.global {} id fresh (.concrete id parent) start amount).child.outcome=.ok ()) :
    (tree.performBorrowAccessRange (.concrete parent) (Size.ofBytes start) (Size.ofBytes amount) .Read
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).status=.Completed ∧
    ((tree.performBorrowAccessRange (.concrete parent) (Size.ofBytes start) (Size.ofBytes amount) .Read
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).tree.newChild
      (Size.ofBytes start) (.concrete parent) tracker.global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes amount) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).outcome=.ok () := ⟨read,child⟩

/-- The common actual AsMut helper derives the two execution certificates
from its one spatial Strong operation. -/
theorem invoke (budget : Nat) (dispatch : limits.callDispatch=budget+1) : Nonempty (Helper out done) := by
  have facts:=CurrentCallCheckpointMutable.s_operation checkpoint out.result out.source
  have read := facts.2.1
  have child := facts.2.2.1
  change (CurrentCallCheckpointMutable.sOutput checkpoint out.result out.source).access.status=.Completed at read
  change (CurrentCallCheckpointMutable.sOutput checkpoint out.result out.source).child.outcome=.ok () at child
  rw [output_eq out] at read child
  have statuses:=literal_status (entry out).allocation.extra (CurrentCallCheckpointDefaultControl.tracker out)
    out.source.role.backing.id (CurrentCallCheckpointDefaultControl.fresh out) out.tracker.global.nextPointerTag
    (UInt64.ofNat checkpoint.offset) len read child
  exact of_steps out done statuses.1 statuses.2 budget dispatch


theorem helper_output (seed : Helper out done) : seed.output=CurrentCallCheckpointMutable.sOutput checkpoint out.result out.source :=
  seed.literal.trans (output_eq out).symm

/-- The common accepted prefix executes the guard, Default-mut statement,
and the actual AsMut helper on the same selected S operation. -/
theorem prepare (nonzero : count≠0) (within : count≤len/2) (budget : Nat) (dispatch : limits.callDispatch=budget+1) :
    ∃done : CurrentCallCheckpointDefaultControl.Done out,∃seed : Helper out done,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] out.frame out.machine)
        (Storage.withCurrent #[(AsMutUncachedCall.cachedCaller done.frame (valid15 out done))] seed.helper seed.machine) := by
  obtain ⟨done⟩:=CurrentCallCheckpointDefaultControl.prepare out nonzero within
  obtain ⟨seed⟩:=invoke out done budget dispatch
  exact ⟨done,seed,SuccessfulTrace.append done.trace seed.trace⟩

end
end DuplicatePrefix.CurrentCallCheckpointAsMutControl
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointAsMutControl" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved common AsMut caller dependency {dependency}"
