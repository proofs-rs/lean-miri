import duplicate_prefix.CurrentCallSpatialEntry
import duplicate_prefix.CurrentCallSpatialEntryBoolCurrent
import duplicate_prefix.CurrentCallSpatialEntryActivity

/-! Actual post-Bool source resources are assembled from the producer's fixed
cell certificates. Only active source cells are collected; no Bool or ambient
role is inferred from this source-only cover. -/
namespace DuplicatePrefix.CurrentCallSpatialEntryCurrent
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover CurrentCallSpatialSourceInstall
open GeneralBorrowFnEntryRegistration GeneralBorrowExposedNonleafPrimaryPath
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option linter.unusedVariables false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
noncomputable section

variable {options remaining span frames root before tracker ctx offset len source returnOffset ret place}
    {C : CurrentCallSpatialEntry.Conditions options remaining span frames root before tracker ctx offset len source returnOffset ret place}
    {limits count} (out : CurrentCallSpatialEntry.Output C limits count)

def machine : Before := CurrentCallSpatialEntry.finalMachine place _ out.physical
  (CurrentCallSpatialEntry.protectedState C count out.entry out.physical out.fresh out.boolOutput) out.updated

def held : MachineHooks.BorrowState := ⟨out.boolOutput.global,tracker.retagMode⟩

def allocation : Allocation Provenance BorrowTree :=
  if out.src.backing.id=out.dst.backing.id then out.updated else out.src.backing.allocation

theorem source_id : out.src.backing.id=source.backing.id :=
  out.src.id.symm.trans ((congrArg Family.allocation out.sourceFamily).trans rfl)

theorem return_id : out.dst.backing.id=ret.backing.id :=
  out.dst.id.symm.trans ((congrArg Family.allocation out.returnFamily).trans ret.id)

theorem concrete : out.src.family.value.provenance=.concrete source.backing.id (CurrentCallSpatialEntry.sourceOutput C).tag := by
  rw [out.sourceFamily]
  rfl

def index : Fin out.src.backing.cells.size := CurrentCallSpatialReturnFrame.fallbackIndex out.src C.positive

theorem overlap : CurrentCallSpatialSourceCover.Active out.src (index out) :=
  CurrentCallSpatialReturnFrame.fallbackOverlap out.src C.positive

def grant : UniIndex := (out.src.roles (index out) (overlap out)).grant

theorem grant_eq (i : Fin out.src.backing.cells.size) (active : CurrentCallSpatialSourceCover.Active out.src i) :
    (out.src.roles i active).grant=grant out :=
  CurrentCallSpatialCover.concrete_grant_eq (out.src.roles i active).binding
    (out.src.roles (index out) (overlap out)).binding (concrete out) (concrete out)

def completion (i : Fin out.src.backing.cells.size) : Completion :=
  if out.src.backing.id=out.dst.backing.id then
    S05ConcreteProtectedChildCompletion.extend out.src.backing.cells[i].completion out.boolChild
      (out.dst.roles (CurrentCallSpatialReturnFrame.returnIndex out.dst) (CurrentCallSpatialReturnFrame.returnOverlap out.dst)).grant
  else out.src.backing.cells[i].completion

/-- One representative supplies structural/issuance facts for an explicitly
fixed completion. Availability below still uses every requested byte. -/
def update (i : Fin out.src.backing.cells.size) (active : CurrentCallSpatialSourceCover.Active out.src i) :
    CurrentCallSpatialSourceCover.Update out.src (machine out) (held out) (allocation out) out.src.family (grant out) i active := by
  classical
  apply Classical.choice
  have pointExists:=active
  obtain ⟨byte,request,cell⟩:=pointExists
  obtain ⟨data,Q,allocationEq,pointerEq,completionEq⟩:=out.sourceFrames i active byte request cell
  have parents : ParentInterpretation (allocation out).extra (completion out i) := by
    simpa only [allocation,completion,allocationEq,completionEq] using Q.parents
  refine ⟨⟨⟨out.src.backing.cells[i].offset,out.src.backing.cells[i].length,completion out i,parents⟩,rfl,rfl,?_,?_,?_⟩⟩
  · simpa only [allocation,allocationEq,pointerEq,grant_eq out i active,Family.at] using Q.binding
  · simpa only [machine,held,allocation,completion,allocationEq,pointerEq,completionEq,grant_eq out i active,Family.at] using Q.issued
  · intro point pointRequest pointCell
    obtain ⟨_,R,allocEq,pointerEq,preciseEq⟩:=out.sourceFrames i active point pointRequest pointCell
    have atPoint : Window out.src.backing.id point.2 1 point:=⟨pointRequest.1,by omega,by omega⟩
    have result:=R.window point atPoint
    simpa only [held,allocation,completion,allocEq,pointerEq,preciseEq,grant_eq out i active,Family.at,demandOf,reduceCtorEq,ite_false] using result

theorem present : Present (ActualWorld (machine out)) out.src.backing.id (allocation out) := by
  obtain ⟨byte,request,cell⟩:=overlap out
  obtain ⟨_,Q,allocEq,_,_⟩:=out.sourceFrames (index out) (overlap out) byte request cell
  simpa only [machine,allocation,allocEq] using Q.present

/-- The SAME explicit completion assignment and common concrete family are
retained in the ACTUAL post-write world. This context is source-only. -/
def context := CurrentCallSpatialSourceCover.context out.src (present out) (update out)

def role : RoleCover (machine out) (held out) (context out) .mut offset len.toNat :=
  CurrentCallSpatialSourceCover.assemble out.src (present out) (update out) out.src.id

theorem family : (role out).family=out.src.family := rfl

theorem source_backing : out.src.backing=CurrentCallSpatialJointInstall.sourceBacking source C.positive C.borrowFrame C.fresh
    (UInt64.ofNat offset) len out.entry out.allocation out.child out.models := by
  exact CurrentCallSpatialCover.Context.same_backing
    (CurrentCallSpatialJointInstall.context source C.positive C.borrowFrame C.fresh (UInt64.ofNat offset) len
      out.entry out.allocation out.child out.models) out.src.backingAt
    (CurrentCallSpatialJointInstall.source_member source C.positive C.borrowFrame C.fresh (UInt64.ofNat offset) len
      out.entry out.allocation out.child out.models) (source_id out)

theorem source_allocation : out.src.backing.allocation=source.backing.allocation.setExtra (CurrentCallSpatialEntry.sourceOutput C).child.tree :=
  congrArg AllocationCover.allocation (source_backing out)

def tree : BorrowTree := if out.physical.id=source.backing.id then out.updated.extra else (CurrentCallSpatialEntry.sourceOutput C).child.tree

theorem allocation_tree : (allocation out).extra=tree out := by
  have iffId : out.src.backing.id=out.dst.backing.id ↔out.physical.id=source.backing.id := by
    constructor
    · intro same;exact out.physicalId.trans (same.symm.trans (source_id out))
    · intro same;exact (source_id out).trans (same.symm.trans out.physicalId)
  by_cases same : out.physical.id=source.backing.id
  · simp only [allocation,tree,ite_eq_left same,ite_eq_left (iffId.mpr same)]
  · simp only [allocation,tree,ite_eq_right same,ite_eq_right (fun eq=>same (iffId.mp eq)),source_allocation]
    rfl

theorem runtime : DuplicatePrefixBorrowContract.RuntimeFacts (allocation out).extra out.boolOutput.global := by
  by_cases same : out.src.backing.id=out.dst.backing.id
  · simpa only [allocation,ite_eq_left same] using out.updatedRuntime
  · rw [allocation,ite_eq_right same,source_allocation]
    change DuplicatePrefixBorrowContract.RuntimeFacts (CurrentCallSpatialEntry.sourceOutput C).child.tree out.boolOutput.global
    obtain ⟨_,_,_,current,_,_⟩:=GeneralBorrowFnEntryRegistrationRuntime.prepare
      (CurrentCallSpatialEntry.sourceOutput C).child.tree (CurrentCallSpatialEntry.sourceOutput C).global
      (CurrentCallSpatialEntry.sourceOutput C).frame out.physical.id out.fresh out.sourceRuntime
    rw [out.boolGlobal]
    exact current

def sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
  if out.physical.id=source.backing.id then {out.physical.entry with allocation:=out.updated}
  else {out.entry with allocation:=out.entry.allocation.setExtra (CurrentCallSpatialEntry.sourceOutput C).child.tree}

private theorem lookup_other (memory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (target changed : AllocId) (entry next : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (different : changed≠target) (live : memory.live.find? (fun row=>row.1==target)=some (target,entry)) :
    ((memory.live.filter (fun row=>row.1!=changed)).push (changed,next)).find? (fun row=>row.1==target)=some (target,entry) := by
  rw [Array.find?_push,Array.find?_filter]
  have predicate : (fun row : AllocId×LocalAllocation Provenance BorrowTree MiriMemoryKind=>decide ((row.1!=changed)=true∧(row.1==target)=true))=(fun row=>row.1==target) := by
    funext row
    by_cases hit : row.1=target
    · simp [hit,Ne.symm different]
    · simp [hit]
  rw [predicate,live]
  simp [different]

theorem live : (machine out).memory.live.find? (fun row=>row.1==out.src.backing.id)=some (out.src.backing.id,sourceEntry out) := by
  rw [source_id]
  by_cases same : out.physical.id=source.backing.id
  · rw [sourceEntry,ite_eq_left same]
    have found:=CurrentCallSpatialEntryBoolCurrent.live out
    simpa only [same,CurrentCallSpatialEntryBoolCurrent.machine,machine] using found
  · rw [sourceEntry,ite_eq_right same]
    let stage:=copiedMachine source C.borrowFrame C.fresh (UInt64.ofNat offset) len out.entry
    let entry:={out.entry with allocation:=out.entry.allocation.setExtra (CurrentCallSpatialEntry.sourceOutput C).child.tree}
    have old : stage.memory.live.find? (fun row=>row.1==source.backing.id)=some (source.backing.id,entry) :=
      MemoryCopyBridge.live_lookup_replaced before.memory source.backing.id _
    have middle:=lookup_other stage.memory source.backing.id out.physical.id entry
      {out.physical.entry with allocation:=out.physical.entry.allocation.setExtra out.boolOutput.child.tree} same old
    exact lookup_other (RetagEntry.updatedMemory stage.memory out.physical.id out.physical.entry out.boolOutput.child.tree)
      source.backing.id out.physical.id entry {out.physical.entry with allocation:=out.updated} same middle

theorem entry_allocation : (sourceEntry out).allocation=allocation out := by
  have iffId : out.src.backing.id=out.dst.backing.id ↔out.physical.id=source.backing.id := by
    constructor
    · intro same;exact out.physicalId.trans (same.symm.trans (source_id out))
    · intro same;exact (source_id out).trans (same.symm.trans out.physicalId)
  by_cases same : out.physical.id=source.backing.id
  · simp only [sourceEntry,allocation,ite_eq_left same,ite_eq_left (iffId.mpr same)]
  · simp only [sourceEntry,allocation,ite_eq_right same,ite_eq_right (fun eq=>same (iffId.mp eq)),source_allocation,out.allocation]

theorem node : ∃node,(allocation out).extra.nodes.get out.child=some node ∧node.tag=(CurrentCallSpatialEntry.sourceOutput C).tag ∧
    node.children=#[] ∧node.isExposed=false ∧GeneralBorrowFreshActiveWithin.ActiveWithin (allocation out).extra out.child .Write
      (UInt64.ofNat offset) ((UInt64.ofNat offset)+len) := by
  rw [allocation_tree]
  exact CurrentCallSpatialEntryActivity.current out

theorem distinct : (allocation out).extra.roots.toList.Nodup := by
  by_cases same : out.src.backing.id=out.dst.backing.id
  · simpa only [allocation,ite_eq_left same] using CurrentCallSpatialEntryBoolCurrent.roots out
  · rw [allocation,ite_eq_right same,source_allocation]
    let row:=(source.backing.id,{out.entry with allocation:=out.entry.allocation.setExtra (CurrentCallSpatialEntry.sourceOutput C).child.tree})
    have found : (copiedMachine source C.borrowFrame C.fresh (UInt64.ofNat offset) len out.entry).memory.live.find? (fun r=>r.1==source.backing.id)=some row :=
      MemoryCopyBridge.live_lookup_replaced before.memory source.backing.id _
    exact out.sourceTracked.roots row (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some found))

theorem short : (allocation out).extra.nodes.size<65536 := by
  by_cases same : out.src.backing.id=out.dst.backing.id
  · simpa only [allocation,ite_eq_left same] using CurrentCallSpatialEntryBoolCurrent.short out
  · rw [allocation,ite_eq_right same,source_allocation]
    change (CurrentCallSpatialEntry.sourceOutput C).child.tree.nodes.size<65536
    have growth:=out.sourceGrowth
    have room:=C.sourceRoom
    omega

end
end DuplicatePrefix.CurrentCallSpatialEntryCurrent



open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallSpatialEntryCurrent.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved spatial count-zero support dependency {dependency}"
