import duplicate_prefix.MetadataOutputFacts
namespace DuplicatePrefix.MetadataOutputThread
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.Concurrency
open MetadataCallSummary MetadataUncachedCall
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem compute_triple_bounded (first second done : CompilerFrameContext.ActualFrame) :
    ∃ index, index < 2 ∧ FrameRelevance.computeTop ⟨#[first,second,done]⟩ 1 = some index := by
  simp [FrameRelevance.computeTop,List.range_succ,List.range_zero,Id.run]
  split
  · exact ⟨1,by decide,rfl⟩
  · split
    · exact ⟨0,by decide,rfl⟩
    · by_cases better : second.extra.userRelevance < first.extra.userRelevance
      · refine ⟨0,by decide,?_⟩
        simp [bind,pure,better]
      · refine ⟨1,by decide,?_⟩
        simp [bind,pure,better]

theorem active_bounded_root (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (root caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (valid : 0 < caller.locals.size)
    (current done : CompilerFrameContext.ActualFrame) (thread : ThreadRecord)
    (active : machine.threads.activeThread? = some thread)
    (index : Nat) (bound : index < 2) (cached : thread.topUserRelevantFrame = some index) :
    ∃ finalIndex, finalIndex < 2 ∧
      (outputMachine options remaining span #[root] caller machine valid current done thread).threads.activeThread? =
        some {thread with topUserRelevantFrame := some finalIndex} := by
  have known := MetadataPushFacts.active options remaining span #[root] (cachedCaller caller valid) machine current thread active
  let helperThread := PushThread.after thread 2 (MetadataFrame.rank options.userRelevantCrates) current.extra.userRelevance
  let post := PtrMetadataReturn.accountedMachine options remaining span
    (MetadataPushFacts.posted options remaining span #[root] (cachedCaller caller valid) machine current)
  have postActive : post.threads.activeThread? = some helperThread := known
  by_cases higher : MetadataFrame.rank options.userRelevantCrates >= current.extra.userRelevance
  · obtain ⟨finalIndex,finalBound,compute⟩ := compute_triple_bounded root (cachedCaller caller valid) done
    have after := MetadataOutputFacts.relevance_active (#[root].push (cachedCaller caller valid)) done post helperThread postActive
    change (GenericPopFrame.afterRelevance (#[root].push (cachedCaller caller valid)) done post).threads.activeThread? =
      some {helperThread with topUserRelevantFrame := FrameRelevance.computeTop ⟨#[root,cachedCaller caller valid,done]⟩ 1} at after
    rw [compute] at after
    refine ⟨finalIndex,finalBound,?_⟩
    simpa only [outputMachine,PtrMetadataReturn.poppedMachine,GenericPopFrame.afterRelevanceAt,helperThread,
      PushThread.after,ite_eq_left higher,Array.size_singleton,Array.size_push,Option.getD_some,beq_self_eq_true,↓reduceIte] using after
  · have restored : {thread with topUserRelevantFrame := some index} = thread := by rw [←cached]
    refine ⟨index,bound,?_⟩
    have notCurrent : index ≠ 2 := by omega
    simpa only [outputMachine,PtrMetadataReturn.poppedMachine,GenericPopFrame.afterRelevanceAt,helperThread,
      PushThread.after,ite_eq_right higher,Array.size_singleton,Array.size_push,cached,Option.getD_some,
      beq_eq_false_iff_ne.mpr notCurrent,ite_eq_right notCurrent,↓reduceIte,restored] using postActive
end
end DuplicatePrefix.MetadataOutputThread

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.MetadataOutputThread." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved exact metadata thread dependency {dependency}"
