import duplicate_prefix.CurrentCallResourceSourceAfterBool

namespace DuplicatePrefix.CurrentCallResourceSourceFinal
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization GeneralBorrowFnEntryRegistration
open CurrentCallResourceEntryBody
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

variable {options remaining span frames root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span frames root before tracker data owner id offset len W place}
    (out : Output limits C count)

open ReturnProtection

theorem same_live (same : out.physical.id=id) :
    out.finalMachine.memory.live.find? (fun row=>row.1==id)=some (id,{out.physical.entry with allocation:=out.updated}) := by
  rw [out.finalMachineEq]
  have found := MemoryCopyBridge.live_lookup_replaced
    (borrowedState frames (RootFrameData.atSpan out.argsRoot ⟨601⟩).frame out.sourceOutput.frame out.sourceMachine
      ⟨out.sourceOutput.global,tracker.retagMode⟩ out.returnRoom out.physical.id out.physical.entry out.boolOutput.child.tree).machine.memory
    out.physical.id {out.physical.entry with allocation:=out.updated}
  simpa only [same] using found

private theorem lookup_other (memory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (target changed : AllocId) (entry next : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (different : changed≠target) (live : memory.live.find? (fun row=>row.1==target)=some (target,entry)) :
    ((memory.live.filter (fun row=>row.1!=changed)).push (changed,next)).find? (fun row=>row.1==target)=some (target,entry) := by
  rw [Array.find?_push,Array.find?_filter]
  have predicate : (fun row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind =>
      decide ((row.1!=changed)=true ∧ (row.1==target)=true))=(fun row=>row.1==target) := by
    funext row
    by_cases hit : row.1=target
    · simp [hit,Ne.symm different]
    · simp [hit]
  rw [predicate,live]
  simp [different]

theorem different_live (different : out.physical.id≠id) :
    out.finalMachine.memory.live.find? (fun row=>row.1==id)=some (id,
      {out.sourceEntry with allocation:=out.sourceEntry.allocation.setExtra out.sourceOutput.child.tree}) := by
  rw [out.finalMachineEq]
  apply lookup_other _ _ _ _ _ different
  change (RetagEntry.updatedMemory out.sourceMachine.memory out.physical.id out.physical.entry out.boolOutput.child.tree).live.find? _ = _
  apply lookup_other _ _ _ _ _ different
  exact CurrentCallResourceSourceAfterBool.source_live out

/-- The actual current source row, including Bool byte changes when the roles
share an allocation. -/
def entry : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
  if out.physical.id=id then {out.physical.entry with allocation:=out.updated}
  else {out.sourceEntry with allocation:=out.sourceEntry.allocation.setExtra out.sourceOutput.child.tree}

def completion : Completion := if out.physical.id=id then
  S05ConcreteProtectedChildCompletion.extend out.R.completion out.boolChild C.V.pointer.grant
  else CurrentCallResourceSourceAfterBool.sourceC out

theorem live : out.finalMachine.memory.live.find? (fun row=>row.1==id)=some (id,entry out) := by
  by_cases same : out.physical.id=id
  · simpa [entry,same] using same_live out same
  · simpa [entry,same] using different_live out same

theorem present : Present (ActualWorld out.finalMachine) id (entry out).allocation := by
  simp only [Present,ActualWorld,Array.toList_map]
  exact List.mem_map.mpr ⟨(id,entry out),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some (live out)),rfl⟩

theorem runtime : DuplicatePrefixBorrowContract.RuntimeFacts (entry out).allocation.extra out.boolOutput.global :=
  out.finalRuntime (id,entry out) (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some (live out)))

theorem roots : (entry out).allocation.extra.roots.toList.Nodup :=
  out.finalRoots (id,entry out) (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some (live out)))

theorem highwater : GeneralBorrowForestTagHighWater.Below (entry out).allocation.extra
    out.boolOutput.global.protectedTags out.boolOutput.global.nextPointerTag :=
  out.finalHighwater (id,entry out) (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some (live out)))

theorem binding : PointerBinds (entry out).allocation (CurrentCallResourceSourceAfterBool.pointer out) := by
  by_cases same : out.physical.id=id
  · simpa [entry,same] using CurrentCallResourceSourceAfterBool.same_binding out same
  · simpa [entry,same,out.sourceAllocation,CurrentCallResourceSourceAfterBool.pointer] using out.sourceWitness.binding

theorem parents : ParentInterpretation (entry out).allocation.extra (completion out) := by
  by_cases same : out.physical.id=id
  · simpa [entry,completion,same] using out.afterParents
  · simpa [entry,completion,same,out.sourceAllocation,CurrentCallResourceSourceAfterBool.sourceC,Allocation.setExtra,Allocation.mapExtra] using out.sourceWitness.parents

theorem window (byte : CandidateFreezeContentResources.Byte) (inside : Window id offset len.toNat byte) :
    byte.2 < (entry out).allocation.len ∧ Embeds (entry out).allocation out.boolOutput.global.protectedTags
      (completion out) out.sourceChild byte.2 .exclusive := by
  by_cases same : out.physical.id=id
  · simpa [entry,completion,same] using CurrentCallResourceSourceAfterBool.same_window out same byte inside
  · simpa [entry,completion,same,out.sourceAllocation,Allocation.setExtra,Allocation.mapExtra,Allocation.len] using
      CurrentCallResourceSourceAfterBool.registered_source_window out byte inside

theorem different_issued (different : out.physical.id≠id) :
    SpatialDelegation out.finalMachine ⟨out.boolOutput.global,tracker.retagMode⟩ id
      (entry out).allocation (completion out) out.sourceChild := by
  have allocation : (entry out).allocation=W.allocation.setExtra out.sourceOutput.child.tree := by
    simp [entry,different,out.sourceAllocation]
  have currentPresent := present out
  rw [allocation] at currentPresent ⊢
  simp only [completion,ite_eq_right different]
  apply CurrentCallAllocationLicense.spatial (CurrentCallResourceSourceAfterBool.source_issued out)
    out.finalMachine ⟨out.boolOutput.global,tracker.retagMode⟩ _ currentPresent
  · rw [out.boolGlobal]
    rfl
  · rfl
  · rfl
  · rfl
  · intro position root found
    exact found
  · intro index node found
    exact ⟨node,found,rfl,rfl,rfl,rfl⟩
  · intro root origin edge
    exact edge

theorem same_issued (same : out.physical.id=id) :
    SpatialDelegation out.finalMachine ⟨out.boolOutput.global,tracker.retagMode⟩ id
      (entry out).allocation (completion out) out.sourceChild := by
  have frame := CurrentCallResourceSourceAfterBool.same_frame out same
  have currentPresent := present out
  have allocation : (entry out).allocation=out.updated := by simp [entry,same]
  rw [allocation] at currentPresent ⊢
  simp only [completion,ite_eq_left same]
  apply CurrentCallAllocationLicense.spatial (CurrentCallResourceSourceAfterBool.source_issued out)
    out.finalMachine ⟨out.boolOutput.global,tracker.retagMode⟩ _ currentPresent
  · rw [out.boolGlobal];rfl
  · rw [out.updatedLength,CurrentCallResourceSourceAfterBool.same_entry out same]
    simp only [out.sourceAllocation,Allocation.setExtra,Allocation.mapExtra,Allocation.len]
  · rw [out.updatedSize,CurrentCallResourceSourceAfterBool.same_entry out same]
    simp only [out.sourceAllocation]
  · exact frame.capacity
  · exact frame.roots
  · exact frame.nodes
  · exact frame.edges

theorem issued : SpatialDelegation out.finalMachine ⟨out.boolOutput.global,tracker.retagMode⟩ id
    (entry out).allocation (completion out) out.sourceChild := by
  by_cases same : out.physical.id=id
  · exact same_issued out same
  · exact different_issued out same

/-- Technical backend dictionaries only: these indices assert no content-owner
freshness, parent suspension, or whole post-call denotation. -/
private def viewData : Identities :=
  {data with interpretation:={data.interpretation with
    pointers:=data.interpretation.pointers.push (CurrentCallResourceSourceAfterBool.pointer out)
    loans:=data.interpretation.loans.push ⟨data.interpretation.pointers.size,some owner,W.loan.depth+1⟩
    precise:=data.interpretation.precise.push (id,{W.precise with completion:=completion out})}}

private def view : UniformWindow out.finalMachine ⟨out.boolOutput.global,tracker.retagMode⟩ (viewData out)
    data.interpretation.loans.size id offset len.toNat .mut where
  loan:=⟨data.interpretation.pointers.size,some owner,W.loan.depth+1⟩
  pointer:=CurrentCallResourceSourceAfterBool.pointer out
  allocation:=(entry out).allocation
  precise:={W.precise with completion:=completion out}
  loanAt:=by simp [viewData]
  pointerAt:=by simp [viewData]
  pointerId:=rfl
  present:=present out
  preciseAt:=by simp [viewData]
  binding:=binding out
  issued:=issued out
  parents:=parents out
  window:=window out

/-- The actual current q grant, with unchanged pointer identity, immediately
supplies the shared-reference resource frontend. No caller interpretation is
rewritten or asserted valid. -/
theorem current : ∃ nextData nextOwner,
    ∃ Q : UniformWindow out.finalMachine ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut,
      Q.pointer=CurrentCallResourceSourceAfterBool.pointer out ∧ Q.allocation=(entry out).allocation ∧
      Q.precise.completion=completion out :=
  ⟨viewData out,data.interpretation.loans.size,view out,rfl,rfl,rfl⟩

end
end DuplicatePrefix.CurrentCallResourceSourceFinal
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceSourceFinal" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved source-final dependency {dependency}"
