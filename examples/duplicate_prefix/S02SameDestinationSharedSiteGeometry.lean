import duplicate_prefix.S02SameDestinationSharedFullSite
import duplicate_prefix.S02SameDestinationMachineGeometry
import duplicate_prefix.S02SeparateDestinationTickLedger

namespace DuplicatePrefix.S02SameDestinationSharedSiteGeometry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- The actual call's address/type/control geometry survives the pure-prefix accounting tick. -/
theorem after_tick
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (sameAllocation : id = input.contract.destination.id)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag)
    (installed : CompilerFrameContext.ActualFrame)
    (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (actual : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] installed post)) :
    let machine := RootZeroCompleteState.tick options remaining span post
    machine.user.addresses = before.user.addresses ∧
    machine.user.payload.payload.user.types = before.user.payload.payload.user.types ∧
    machine.user.payload.payload.user.backend = .none ∧
    machine.user.payload.ghost = false ∧ machine.user.payload.validation = .Shallow ∧
    ((config options (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false ∧
    ((config options (remaining+1) span).terminators.getControl machine.user).gcInterval = 0 ∧
    machine.threads.fixedScheduling = true ∧ machine.dataRace = none ∧
    ∃ thread, machine.threads.activeThread? = some thread ∧ thread.topUserRelevantFrame = some 0 := by
  obtain ⟨_reference,_tracker,otherFrame,otherPost,otherActual,_tracked,_mode,ghost,shallow,
    unchecked,noGc,fixed,race,addresses,types,backend,thread⟩ :=
    S02SameDestinationMachineGeometry.after_exact id tag address len count input nonempty
      sameAllocation returnTag returnConcrete
  have same : Storage.withCurrent #[] otherFrame otherPost = Storage.withCurrent #[] installed post :=
    (EStateM.Result.ok.inj (otherActual.symm.trans actual)).2
  have postEq : otherPost = post := congrArg (fun s : RootState => s.machine) same
  subst otherPost
  obtain ⟨_memory,_borrow,tickRace,tickThreads,tickAddresses,tickTypes,tickBackend,_extras⟩ :=
    S02SeparateDestinationTickLedger.preserved options remaining span post
  obtain ⟨thread,active,topZero⟩ := thread
  refine ⟨tickAddresses.trans addresses,tickTypes.trans types,tickBackend.trans backend,?_,?_,?_,?_,
    tickThreads ▸ fixed,tickRace ▸ race,?_⟩
  · rw [RootZeroCompleteState.tick_ghost]
    exact ghost
  · rw [RootZeroCompleteState.tick_shallow]
    exact shallow
  · exact (RootZeroCompleteState.tick_flags options remaining span post).1.trans unchecked
  · exact (RootZeroCompleteState.tick_flags options remaining span post).2.trans noGc
  · exact ⟨thread,by rw [tickThreads]; exact active,topZero⟩

end
end DuplicatePrefix.S02SameDestinationSharedSiteGeometry

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SameDestinationSharedSiteGeometry.after_tick) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate site geometry dependency {dependency}"
