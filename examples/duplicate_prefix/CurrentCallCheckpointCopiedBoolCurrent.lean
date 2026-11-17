import duplicate_prefix.CurrentCallCheckpointCopyBoolFrame
import duplicate_prefix.CurrentCallCheckpointCopyBoolInstall
import duplicate_prefix.CurrentCallCheckpointCopyAccess
namespace DuplicatePrefix.CurrentCallCheckpointCopiedBoolCurrent
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallPostEntryCheckpoint GeneralRangeMapOrigins S05CompletedAncestryReadMutable
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section
variable {options remaining span len count place limits} {cp : Checkpoint options remaining span len count place}
  (out : CurrentCallCheckpointRoot3.Output cp limits) (done : CurrentCallCheckpointDefaultControl.Done out)
  (seed : CurrentCallCheckpointAsMutControl.Helper out done) (returned : CurrentCallCheckpointAsMutReturn.Returned seed)
  (data : CurrentCallCheckpointAsMutSource.Data out done seed returned)
  (B : CurrentCallCheckpointAcceptedBoolCurrent.Packet out done seed returned)
  (access : CurrentCallCheckpointCopyAccess.Access out done seed returned data)

private theorem setExtra_twice (allocation : Allocation Provenance BorrowTree) (first second : BorrowTree) :
    (allocation.setExtra first).setExtra second=allocation.setExtra second:=by cases allocation;rfl

theorem allocation_same (same : cp.output.id=cp.source.role.backing.id) :
    B.current.window.allocation=data.role.backing.allocation := by
  rw [B.allocated]
  dsimp only [CurrentCallCheckpointAcceptedBoolCurrent.tree]
  rw [ite_eq_left same,CurrentCallCheckpointAcceptedBoolFrame.allocation_same cp out.result out.source out.target same,data.allocation]
  change out.source.role.backing.allocation.setExtra (CurrentCallCheckpointAsMutReturn.releasedTree seed)=
    ((CurrentCallCheckpointDefaultControl.entry out).allocation.setExtra (CurrentCallCheckpointDefaultControl.tree out)).setExtra
      (CurrentCallCheckpointAsMutReturn.releasedTree seed)
  rw [setExtra_twice]
  exact congrArg (fun allocation : Allocation Provenance BorrowTree=>allocation.setExtra (CurrentCallCheckpointAsMutReturn.releasedTree seed)) out.source.allocation

include data access in
/-- The SAME concrete copy's prefix Read and adjacent Write preserve Bool
rights under its own completion, with no source rights under that completion. -/
theorem same_raw (same : cp.output.id=cp.source.role.backing.id) (within : count≤len/2) :
    ParentInterpretation (CurrentCallCheckpointCopyPrefix.writeAccess out done seed).tree B.current.window.precise.completion ∧
    OwnedOn (Authority (CurrentCallCheckpointCopyPrefix.writeAccess out done seed).tree B.current.window.precise.completion
      (CurrentCallCheckpointAsMutReturn.postTracker seed).global.protectedTags B.current.window.pointer.grant)
      B.current.physical.offset (B.current.physical.offset+1) (CurrentCallCheckpointCopyPrefix.writeAccess out done seed).tree.locations ∧
    (CurrentCallCheckpointCopyPrefix.writeAccess out done seed).tree.nodeAt B.current.window.pointer.grant=some B.current.node ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin (CurrentCallCheckpointCopyPrefix.writeAccess out done seed).tree B.current.window.pointer.grant .Write
      B.current.physical.offset (B.current.physical.offset+1) := by
  have allocation:=allocation_same out done seed returned data B same
  have sourceBounds:=CurrentCallCheckpointCopyAccess.role_bounds data.role cp.source.positive
  have startEq:=(CurrentCallCheckpointShared.start_eq cp)
  have fullBounds : (UInt64.ofNat cp.offset).toNat+len.toNat≤data.role.backing.allocation.extra.locations.size.bytes.toNat:=by rw [startEq];exact sourceBounds
  have numeric:=UInt64.le_iff_toNat_le.mp within
  rw [UInt64.toNat_div] at numeric
  change count.toNat≤len.toNat/2 at numeric
  have fits : cp.offset+len.toNat<2^64:=Nat.lt_of_le_of_lt sourceBounds data.role.backing.allocation.extra.locations.size.bytes.toNat_lt
  have fullStop : (UInt64.ofNat cp.offset+len).toNat=cp.offset+len.toNat:=by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt (by rw [startEq];exact fits),startEq]
  have middle : (UInt64.ofNat cp.offset+count).toNat=cp.offset+count.toNat:=by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt (by rw [startEq];omega),startEq]
  have readStop : (UInt64.ofNat cp.offset+count).toNat=cp.offset+count.toNat:=middle
  have writeStop : (UInt64.ofNat cp.offset+count+count).toNat=cp.offset+count.toNat+count.toNat:=by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt (by rw [middle];omega),middle]
  have positive:=cp.source.positive
  obtain ⟨i,cell⟩:=data.role.covered (data.role.backing.id,cp.offset) ⟨rfl,Nat.le_refl _,by omega⟩
  let overlap : CurrentCallSpatialSourceCover.Active data.role i:=⟨_,⟨rfl,Nat.le_refl _,by omega⟩,cell⟩
  obtain ⟨sourceNode,sourceAt,mapped,binding⟩:=(data.role.roles i overlap).binding
  have concrete:=CurrentCallCheckpointAsMutSourceMetadata.concrete out done seed returned data
  change (match data.role.family.value.provenance with | .concrete id tag=>id=data.role.family.allocation ∧tag=sourceNode.tag | .wildcard=>sourceNode.isExposed=true) at binding
  rw [concrete] at binding
  have sourceTag : sourceNode.tag=seed.output.tag:=binding.2.symm
  have tagged : data.role.backing.allocation.extra.indexOfTag seed.output.tag=some (data.role.roles i overlap).grant:=by rw [←sourceTag];exact mapped
  have targetAt : data.role.backing.allocation.extra.nodeAt B.current.window.pointer.grant=some B.current.node:=by rw [←allocation];exact B.current.nodeAt
  have different : B.current.window.pointer.grant≠(data.role.roles i overlap).grant:=by
    intro equal
    rw [equal] at targetAt
    have nodeEq:=Option.some.inj (targetAt.symm.trans sourceAt)
    have tagEq := (congrArg TreeNode.tag nodeEq).trans sourceTag
    have oldBelow:=GeneralBorrowParentTagInvariant.parent_below_fresh _ _ out.target.current.runtime _ out.target.current.node out.target.current.nodeAt
    have oldNumeric:=UInt64.lt_iff_toNat_lt.mp oldBelow
    have successor:=GenericFunctionEntryNumerics.successor_value (CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag
      (CurrentCallCheckpointAcceptedBoolFrame.room cp out.result out.source)
    change (CurrentCallCheckpointMutable.sOutput cp out.result out.source).tag.value.toNat=
      (CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag.value.toNat+1 at successor
    have outputEq:=congrArg (fun output : GeneralBorrowForestFnEntry.Output=>output.tag.value.toNat) (CurrentCallCheckpointAsMutControl.helper_output out done seed)
    have tagNumeric:=congrArg (fun tag : BorTag=>tag.value.toNat) (B.tag.symm.trans tagEq)
    change out.target.current.node.tag.value.toNat<(CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag.value.toNat at oldNumeric
    omega
  have parents : ParentInterpretation data.role.backing.allocation.extra B.current.window.precise.completion:=by rw [←allocation];exact B.current.window.parents
  have endSmall:=Nat.lt_of_le_of_lt B.current.physical.bounds B.current.physical.capacity.toNat_lt
  have endEq : (B.current.physical.offset+1).toNat=B.current.offset+1:=by
    rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt endSmall,B.current.physicalOffset]
  have owned:=(checkpoint_bool_rule "CurrentCallExclusiveWindowFrame.window_owned") B.current.window rfl B.current.runtime
    B.current.physical.offset (B.current.physical.offset+1) (by have eq:=B.current.physicalOffset;omega) (by rw [endEq];exact Nat.le_refl _)
  have sourceOwned : OwnedOn (Authority data.role.backing.allocation.extra B.current.window.precise.completion
      (CurrentCallCheckpointAsMutReturn.postTracker seed).global.protectedTags B.current.window.pointer.grant)
      B.current.physical.offset (B.current.physical.offset+1) data.role.backing.allocation.extra.locations:=by rw [←allocation];exact owned
  have sourceActive : GeneralBorrowFreshActiveWithin.ActiveWithin data.role.backing.allocation.extra B.current.window.pointer.grant .Write
      B.current.physical.offset (B.current.physical.offset+1):=by rw [←allocation];exact B.current.activity
  have offsetEq : B.current.physical.offset=cp.output.physical.offset:=UInt64.toNat_inj.mp
    (B.current.physicalOffset.trans (B.offset.trans cp.output.physicalOffset.symm))
  have apart:=CurrentCallCheckpointSharedBoolFrame.checkpoint_apart cp same
  have readApart : ∀point : UInt64,B.current.physical.offset.toNat≤point.toNat→point.toNat<(B.current.physical.offset+1).toNat→
      point.toNat<(UInt64.ofNat cp.offset).toNat∨(UInt64.ofNat cp.offset+count).toNat≤point.toNat:=by
    rw [offsetEq]
    intro point lo hi
    rcases apart with left | right <;>rw [startEq,readStop] <;>omega
  have writeApart : ∀point : UInt64,B.current.physical.offset.toNat≤point.toNat→point.toNat<(B.current.physical.offset+1).toNat→
      point.toNat<(UInt64.ofNat cp.offset+count).toNat∨(UInt64.ofNat cp.offset+count+count).toNat≤point.toNat:=by
    rw [offsetEq]
    intro point lo hi
    rcases apart with left | right <;>rw [middle,writeStop] <;>omega
  have retained:=CurrentCallCheckpointCopyBoolFrame.two data.role data.runtime (CurrentCallCheckpointCopyAccess.entry out done seed)
    (UInt64.ofNat cp.offset) count (UInt64.ofNat cp.offset+count) count (UInt64.ofNat cp.offset) len access.read
    B.current.window.precise.completion parents seed.output.tag (data.role.roles i overlap).grant B.current.window.pointer.grant sourceNode B.current.node
    concrete sourceAt tagged targetAt B.current.leaf B.current.hidden different startEq rfl fullBounds (Nat.le_refl _) (by rw [startEq];omega)
    (by rw [startEq,middle];omega) (by rw [startEq,middle];omega) B.current.physical.offset (B.current.physical.offset+1)
    readApart writeApart sourceOwned sourceActive access.write.tree_eq
  rw [CurrentCallCheckpointCopyAccess.write_eq out done seed returned data access.read] at retained
  exact retained

include access in
/-- Geometry and runtime of the exact two actual accesses. -/
theorem geometry :
    DuplicatePrefixBorrowContract.RuntimeFacts (CurrentCallCheckpointCopyPrefix.writeAccess out done seed).tree
      (CurrentCallCheckpointAsMutReturn.postTracker seed).global ∧
    (CurrentCallCheckpointCopyPrefix.writeAccess out done seed).tree=
      {data.role.backing.allocation.extra with locations:=(CurrentCallCheckpointCopyPrefix.writeAccess out done seed).tree.locations} ∧
    (CurrentCallCheckpointCopyPrefix.writeAccess out done seed).tree.locations.size=data.role.backing.allocation.extra.locations.size := by
  have writeEq:=CurrentCallCheckpointCopyAccess.write_eq out done seed returned data access.read
  have readEq:=CurrentCallCheckpointCopyAccess.read_eq out done seed returned data
  have stageTree:=CurrentCallSpatialSubrangeSequence.ReadStage.tree access.read
  rw [readEq] at stageTree
  have writeShape:=access.write.tree_eq
  rw [writeEq,stageTree] at writeShape
  have readShape:=access.read.shape
  rw [readEq] at readShape
  have capacity:=access.write.capacity
  rw [writeEq,stageTree] at capacity
  have readCapacity:=access.read.capacity
  rw [readEq] at readCapacity
  have runtime:=access.writeRuntime
  rw [writeEq] at runtime
  refine ⟨runtime,?_,capacity.trans readCapacity⟩
  calc
    (CurrentCallCheckpointCopyPrefix.writeAccess out done seed).tree=
      {(CurrentCallCheckpointCopyPrefix.readAccess out done seed).tree with locations:=(CurrentCallCheckpointCopyPrefix.writeAccess out done seed).tree.locations}:=writeShape
    _={data.role.backing.allocation.extra with locations:=(CurrentCallCheckpointCopyPrefix.writeAccess out done seed).tree.locations}:=by rw [readShape]

private theorem live_id {memory : MemoryState Provenance BorrowTree MiriMemoryKind} {oldId newId : AllocId}
    {entry : LocalAllocation Provenance BorrowTree MiriMemoryKind} (equal : oldId=newId)
    (live : memory.live.find? (fun row=>row.1==oldId)=some (oldId,entry)) :
    memory.live.find? (fun row=>row.1==newId)=some (newId,entry):=by cases equal;exact live
private theorem entry_extra_self (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) :
    {entry with allocation:=entry.allocation.setExtra entry.allocation.extra}=entry:=by
  cases entry with
  | mk kind allocation=>cases allocation;rfl

variable (copied : CurrentCallCheckpointCopyPrefix.Copied out done seed returned)

def allocation : Allocation Provenance BorrowTree:=if cp.output.id=cp.source.role.backing.id then copied.allocation else B.current.window.allocation

/-- Actual heap presence is derived from the same physical copy replacement. -/
theorem live : copied.machine.memory.live.find? (fun row=>row.1==B.current.id)=some
    (B.current.id,{B.current.physical.entry with allocation:=allocation out done seed returned B copied}) := by
  by_cases same : cp.output.id=cp.source.role.backing.id
  · have id : B.current.id=out.source.role.backing.id:=B.id.trans (same.trans out.source.id.symm)
    have oldLive:=B.current.physical.live
    rw [B.current.physicalId,id] at oldLive
    have entryEq := congrArg Prod.snd (Option.some.inj (oldLive.symm.trans returned.sourceLive))
    have kindEq:=congrArg (fun entry : LocalAllocation Provenance BorrowTree MiriMemoryKind=>entry.kind) entryEq
    change B.current.physical.entry.kind=(CurrentCallCheckpointAsMutControl.entry out).kind at kindEq
    have rowEq : (⟨(CurrentCallCheckpointAsMutControl.entry out).kind,copied.allocation⟩ : LocalAllocation Provenance BorrowTree MiriMemoryKind)=
        {B.current.physical.entry with allocation:=allocation out done seed returned B copied}:=by
      dsimp only [allocation]
      rw [ite_eq_left same]
      change (⟨(CurrentCallCheckpointAsMutControl.entry out).kind,copied.allocation⟩ : LocalAllocation Provenance BorrowTree MiriMemoryKind)=
        ⟨B.current.physical.entry.kind,copied.allocation⟩
      rw [kindEq]
    have actual:=copied.live
    rw [rowEq] at actual
    exact live_id id.symm actual
  · have different : B.current.id≠out.source.role.backing.id:=by intro eq;apply same;exact B.id.symm.trans (eq.trans out.source.id)
    have oldLive:=B.current.physical.live
    rw [B.current.physicalId] at oldLive
    let newEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind:=⟨(CurrentCallCheckpointAsMutControl.entry out).kind,copied.allocation⟩
    have actual:=StackPopRelease.lookup_commit_other returned.machine.memory out.source.role.backing.id B.current.id
      newEntry B.current.physical.entry copied.allocation.extra different oldLive
    have eta : {newEntry with allocation:=newEntry.allocation.setExtra copied.allocation.extra}=newEntry:=entry_extra_self newEntry
    change (((returned.machine.memory.live.filter (fun row=>row.1!=out.source.role.backing.id)).push
      (out.source.role.backing.id,{newEntry with allocation:=newEntry.allocation.setExtra copied.allocation.extra})).find? (fun row=>row.1==B.current.id))=
      some (B.current.id,B.current.physical.entry) at actual
    rw [eta] at actual
    rw [copied.memory]
    dsimp only [allocation]
    rw [ite_eq_right same,←B.current.physicalAllocation]
    exact actual


structure Packet where
  current : Return copied.machine (CurrentCallCheckpointAsMutReturn.postTracker seed) place
  id : current.id=cp.output.id
  offset : current.offset=cp.output.offset
  pointer : current.window.pointer=B.current.window.pointer
  original : current.original=B.current.original
  allocated : current.window.allocation=allocation out done seed returned B copied
  precise : current.window.precise=B.current.window.precise
  node : current.node=B.current.node

include data access in
/-- Actual sequential copy and physical mutation retain the protected Bool
window and ORIGINAL destination licence on the same final root-9 machine. -/
theorem invoke (within : count≤len/2) : Nonempty (Packet out done seed returned B copied) := by
  have actualLive:=live out done seed returned B copied
  by_cases same : cp.output.id=cp.source.role.backing.id
  · have sourceAllocation:=allocation_same out done seed returned data B same
    have initialEq : CurrentCallCheckpointCopyPrefix.allocation out done seed=B.current.window.allocation:=
      data.allocation.symm.trans sourceAllocation.symm
    obtain ⟨runtime,sourceShape,sourceCapacity⟩:=geometry out done seed returned data access
    obtain ⟨parents,owned,nodeAt,active⟩:=same_raw out done seed returned data B access same within
    have length:=copied.length.trans (congrArg Allocation.len initialEq)
    have bytes:=copied.byteSize.trans (congrArg Allocation.byteSize initialEq)
    have shape : copied.allocation.extra={B.current.window.allocation.extra with locations:=copied.allocation.extra.locations}:=by
      rw [copied.tree]
      rw [←sourceAllocation] at sourceShape
      exact sourceShape
    have capacity : copied.allocation.extra.locations.size=B.current.window.allocation.extra.locations.size:=by
      rw [copied.tree]
      rw [←sourceAllocation] at sourceCapacity
      exact sourceCapacity
    have currentRuntime : DuplicatePrefixBorrowContract.RuntimeFacts copied.allocation.extra (CurrentCallCheckpointAsMutReturn.postTracker seed).global:=by
      rw [copied.tree];exact runtime
    have currentOwned : OwnedOn (Authority copied.allocation.extra B.current.window.precise.completion
        (CurrentCallCheckpointAsMutReturn.postTracker seed).global.protectedTags B.current.window.pointer.grant)
        B.current.physical.offset (B.current.physical.offset+1) copied.allocation.extra.locations:=by rw [copied.tree];exact owned
    have currentActivity : GeneralBorrowFreshActiveWithin.ActiveWithin copied.allocation.extra B.current.window.pointer.grant .Write
        B.current.physical.offset (B.current.physical.offset+1):=by rw [copied.tree];exact active
    dsimp only [allocation] at actualLive
    rw [ite_eq_left same] at actualLive
    obtain ⟨current,id,offset,pointer,original,allocated,precise,node⟩:=CurrentCallCheckpointCopyBoolInstall.install B.current copied.machine copied.allocation
      actualLive copied.addresses copied.extras length bytes shape capacity currentRuntime copied.physical currentOwned currentActivity
    refine ⟨{current:=current,id:=id.trans B.id,offset:=offset.trans B.offset,pointer:=pointer,original:=original,allocated:=?_,precise:=precise,node:=node}⟩
    dsimp only [allocation]
    rw [ite_eq_left same]
    exact allocated
  · have endSmall:=Nat.lt_of_le_of_lt B.current.physical.bounds B.current.physical.capacity.toNat_lt
    have endEq : (B.current.physical.offset+1).toNat=B.current.offset+1:=by
      rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt endSmall,B.current.physicalOffset]
    have owned:=(checkpoint_bool_rule "CurrentCallExclusiveWindowFrame.window_owned") B.current.window rfl B.current.runtime
      B.current.physical.offset (B.current.physical.offset+1) (by have eq:=B.current.physicalOffset;omega) (by rw [endEq];exact Nat.le_refl _)
    have physical : S02SameDestinationAcceptedCopyPhysical.Physical B.current.window.allocation:=by
      refine ⟨?_,?_,?_,?_⟩
      · rw [←B.current.physicalAllocation];exact B.current.physical.mutable
      · rw [←B.current.physicalAllocation];exact B.current.physical.maskValid
      · rw [←B.current.physicalAllocation]
        exact B.current.physical.maskLength.trans B.current.physical.size.symm
      · rw [←B.current.physicalAllocation];exact B.current.physical.pointerBounds
    dsimp only [allocation] at actualLive
    rw [ite_eq_right same] at actualLive
    obtain ⟨current,id,offset,pointer,original,allocated,precise,node⟩:=CurrentCallCheckpointCopyBoolInstall.install B.current copied.machine B.current.window.allocation
      actualLive copied.addresses copied.extras rfl rfl rfl rfl B.current.runtime physical owned B.current.activity
    refine ⟨{current:=current,id:=id.trans B.id,offset:=offset.trans B.offset,pointer:=pointer,original:=original,allocated:=?_,precise:=precise,node:=node}⟩
    dsimp only [allocation]
    rw [ite_eq_right same]
    exact allocated

end
end DuplicatePrefix.CurrentCallCheckpointCopiedBoolCurrent
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointCopiedBoolCurrent" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved current copied Bool dependency {dependency}"
