import duplicate_prefix.CurrentCallPostRole
namespace DuplicatePrefix.CurrentCallPostRoleSource
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization GeneralBorrowFnEntryRegistration CurrentCallPostRole
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- The literal source heap installation retains the original return role,
including when both roles occupy the same allocation. Correlations on equal
allocation IDs are supplied by the one original joint interpretation. -/
theorem installed {before tracker data owner id offset length mode returnOwner returnId returnOffset}
    (W : UniformWindow before tracker data owner id offset length mode)
    (V : UniformWindow before tracker data returnOwner returnId returnOffset 1 .ret)
    (sameAllocation : returnId=id → V.allocation=W.allocation)
    (sameCompletion : returnId=id → V.precise.completion=W.precise.completion)
    (separate : returnId=id → ∀ byte,Window id offset length byte → Window returnId returnOffset 1 byte → False)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (returnRuntime : DuplicatePrefixBorrowContract.RuntimeFacts V.allocation.extra tracker.global)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (highwater : ∀ row∈before.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra
      tracker.global.protectedTags tracker.global.nextPointerTag)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (exclusive : demandOf mode=.exclusive) (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size<65536) (nodeRoom : W.allocation.extra.nodes.size+1≤4294967295)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount≠0) (bounds : start.toNat+amount.toNat≤W.allocation.extra.locations.size.bytes.toNat)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (_live : before.memory.live.find? (fun row=>row.1==id)=some (id,entry)) (allocation : entry.allocation=W.allocation)
    (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex)
    (actual : CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start amount=.ok output)
    (witness : CurrentCallResourceFnEntry.BorrowWitness W output child start amount)
    (tag : output.tag=tracker.global.nextPointerTag) (global : output.global=(registered tracker.global frame id room).1)
    (post : Before) (memory : post.memory.live=(before.memory.live.filter (fun row=>row.1!=id)).push
      (id,{entry with allocation:=entry.allocation.setExtra output.child.tree})) :
    ∃ R : InstalledRole V post ⟨output.global,tracker.retagMode⟩,
      (returnId=id → R.tree=output.child.tree ∧ R.completion=S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) ∧
      (returnId≠id → R.tree=V.allocation.extra ∧ R.completion=V.precise.completion) := by
  by_cases same : returnId=id
  · subst returnId
    have present : Present (ActualWorld post) id (W.allocation.setExtra output.child.tree) := by
      simp only [Present,ActualWorld,Array.toList_map]
      apply List.mem_map.mpr
      refine ⟨(id,{entry with allocation:=entry.allocation.setExtra output.child.tree}),?_,?_⟩
      · apply Array.mem_toList_iff.mpr
        apply Array.mem_of_find?_eq_some
        rw [memory]
        exact MemoryCopyBridge.live_lookup_replaced before.memory id _
      · simp only [allocation]
    obtain ⟨R,tree,completion⟩ := after_source_same W V (sameAllocation rfl) (sameCompletion rfl) (separate rfl)
      runtime state highwater frame room exclusive distinct short nodeRoom start amount startEq amountEq nonzero bounds
      output child actual witness tag global post present
    exact ⟨R,fun _=>⟨tree,completion⟩,fun different=>False.elim (different rfl)⟩
  · have present : Present (ActualWorld post) returnId V.allocation := by
      have original := V.present
      simp only [Present,ActualWorld,Array.toList_map] at original ⊢
      obtain ⟨row,member,rowEq⟩ := List.mem_map.mp original
      have rowId : row.1=returnId := (Prod.mk.inj rowEq).1
      apply List.mem_map.mpr
      refine ⟨row,?_,rowEq⟩
      rw [memory]
      simp only [Array.toList_push,List.mem_append,List.mem_singleton]
      apply Or.inl
      simp only [Array.toList_filter,List.mem_filter]
      exact ⟨member,by simp [rowId,same]⟩
    let Result := fun next : MachineHooks.BorrowState => ∃ R : InstalledRole V post next,
      R.tree=V.allocation.extra ∧ R.completion=V.precise.completion
    have oldResult : Result {tracker with global:=(registered tracker.global frame id room).1} :=
      after_source_unchanged V returnRuntime frame room id post present
    have nextEq : ({tracker with global:=(registered tracker.global frame id room).1} : MachineHooks.BorrowState)=
        ⟨output.global,tracker.retagMode⟩ := by rw [global]
    have result : Result ⟨output.global,tracker.retagMode⟩ := Eq.mp (congrArg Result nextEq) oldResult
    obtain ⟨R,tree,completion⟩ := result
    exact ⟨R,fun equal=>False.elim (same equal),fun _=>⟨tree,completion⟩⟩

end
end DuplicatePrefix.CurrentCallPostRoleSource
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallPostRoleSource" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved installed source-role dependency {dependency}"
