import duplicate_prefix.MetadataOutputThread
namespace DuplicatePrefix.MetadataOutputCacheBound
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.Concurrency
open MetadataCallSummary MetadataUncachedCall
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- With exactly one root below the caller, a metadata helper preserves a
bounded optional relevance cache. An absent cache causes the real relevance
suffix to recompute an index among the two remaining frames. -/
theorem active_cache_bounded_root (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (root caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (valid : 0 < caller.locals.size)
    (current done : CompilerFrameContext.ActualFrame) (thread : ThreadRecord)
    (active : machine.threads.activeThread? = some thread)
    (bound : ∀ index, thread.topUserRelevantFrame = some index → index < 2) :
    ∃ finalThread,
      (outputMachine options remaining span #[root] caller machine valid current done thread).threads.activeThread? = some finalThread ∧
      ∀ index, finalThread.topUserRelevantFrame = some index → index < 2 := by
  cases cached : thread.topUserRelevantFrame with
  | some index =>
    obtain ⟨finalIndex,finalBound,outputActive⟩ := MetadataOutputThread.active_bounded_root options remaining span root caller machine valid
      current done thread active index (bound index cached) cached
    refine ⟨{thread with topUserRelevantFrame := some finalIndex},outputActive,?_⟩
    intro query same
    exact (Option.some.inj same) ▸ finalBound
  | none =>
    have known := MetadataPushFacts.active options remaining span #[root] (cachedCaller caller valid) machine current thread active
    let helperThread := PushThread.after thread 2 (MetadataFrame.rank options.userRelevantCrates) current.extra.userRelevance
    let post := PtrMetadataReturn.accountedMachine options remaining span
      (MetadataPushFacts.posted options remaining span #[root] (cachedCaller caller valid) machine current)
    have postActive : post.threads.activeThread? = some helperThread := known
    have cacheIndex : helperThread.topUserRelevantFrame.getD 2 = 2 := by
      unfold helperThread PushThread.after
      split
      · rfl
      · simp only [cached,Option.getD_none]
    obtain ⟨finalIndex,finalBound,compute⟩ := MetadataOutputThread.compute_triple_bounded root (cachedCaller caller valid) done
    have after := MetadataOutputFacts.relevance_active (#[root].push (cachedCaller caller valid)) done post helperThread postActive
    change (GenericPopFrame.afterRelevance (#[root].push (cachedCaller caller valid)) done post).threads.activeThread? =
      some {helperThread with topUserRelevantFrame := FrameRelevance.computeTop ⟨#[root,cachedCaller caller valid,done]⟩ 1} at after
    rw [compute] at after
    refine ⟨{helperThread with topUserRelevantFrame := some finalIndex},?_,?_⟩
    · change (GenericPopFrame.afterRelevanceAt (#[root].push (cachedCaller caller valid)) done post
        (helperThread.topUserRelevantFrame.getD 2)).threads.activeThread? = _
      rw [cacheIndex]
      simpa only [GenericPopFrame.afterRelevanceAt,Array.size_singleton,Array.size_push,↓reduceIte] using after
    · intro query same
      exact (Option.some.inj same) ▸ finalBound
end
end DuplicatePrefix.MetadataOutputCacheBound
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.MetadataOutputCacheBound." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved metadata optional cache dependency {dependency}"
