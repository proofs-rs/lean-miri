import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableAsMutCallInput
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableAsMutCallState
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open GeneralBorrowExposedScopedInactiveWritableAsMutCallInput
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

structure AccountedFacts {profileMode : ProfileMode} (s : InputFor profileMode) : Prop where
  memory : (accounted s).memory=s.machine.memory
  tracked : (accounted s).borrowTracker=some s.tracker
  race : (accounted s).dataRace=none
  threads : (accounted s).threads=s.machine.threads
  addresses : (accounted s).user.addresses=s.machine.user.addresses
  types : (accounted s).user.payload.payload.user.types=s.machine.user.payload.payload.user.types
  extras : (accounted s).user.payload.payload.user.runtime.extras=s.machine.user.payload.payload.user.runtime.extras
  backend : (accounted s).user.payload.payload.user.backend=.none

theorem accounted_fields {profileMode : ProfileMode} (s : InputFor profileMode) : AccountedFacts s := by
  constructor
  all_goals unfold accounted AsMutPtrReturn.accountedMachine SourceControl.accounted
  all_goals rw [(CanonicalConfigFacts.actual_fields s.options () (s.remaining+1) s.span).terminators]
  all_goals first | rfl | exact s.tracked | exact s.race | exact s.backend

structure PushFacts {profileMode : ProfileMode} (s : InputFor profileMode) : Prop where
  memory : (pushed s).memory=s.machine.memory
  tracked : (pushed s).borrowTracker=some s.tracker
  race : (pushed s).dataRace=none
  ghost : (pushed s).user.payload.ghost=false
  shallow : (pushed s).user.payload.validation=.Shallow
  types : (pushed s).user.payload.payload.user.types=s.machine.user.payload.payload.user.types
  extras : (pushed s).user.payload.payload.user.runtime.extras=s.machine.user.payload.payload.user.runtime.extras
  backend : (pushed s).user.payload.payload.user.backend=.none
  addresses : (pushed s).user.addresses=s.machine.user.addresses
  user : (pushed s).user.payload.payload.user=(accounted s).user.payload.payload.user
  fixed : (pushed s).threads.fixedScheduling=true
  active : (pushed s).threads.activeThread?=some (PushThread.after s.thread 1 (AsMutFrame.rank s.options.userRelevantCrates) (caller s).extra.userRelevance)

theorem pushed_fields {profileMode : ProfileMode} (s : InputFor profileMode) : PushFacts s := by
  have a:=accounted_fields s
  have enabled : (accounted s).threads.activeThread?=some s.thread := by rw [a.threads];exact s.active
  have f:=GeneralBorrowForestAsMutEntryState.push_fields s.options.userRelevantCrates (caller s) (accounted s) (destination s) s.thread enabled
  have user := f.2.2.2.2.2.1
  change (pushed s).user.payload.payload.user=(accounted s).user.payload.payload.user at user
  refine ⟨f.1.trans a.memory,f.2.1.trans a.tracked,f.2.2.1.trans a.race,?_,?_,?_,?_,?_,f.2.2.2.2.2.2.1.trans a.addresses,user,
    f.2.2.2.2.2.2.2.1.trans (by rw [a.threads];exact s.fixed),f.2.2.2.2.2.2.2.2⟩
  · change (pushed s).user.payload.ghost=false
    exact f.2.2.2.1.trans ((AsMutPtrReturn.accounted_ghost s.options s.remaining s.span s.machine).trans s.ghost)
  · exact f.2.2.2.2.1.trans ((AsMutPtrReturn.accounted_validation s.options s.remaining s.span s.machine).trans s.shallow)
  · change (pushed s).user.payload.payload.user.types=_
    rw [user];exact a.types
  · change (pushed s).user.payload.payload.user.runtime.extras=_
    rw [user];exact a.extras
  · change (pushed s).user.payload.payload.user.backend=_
    rw [user];exact a.backend

theorem actual_entry {profileMode : ProfileMode} (s : InputFor profileMode) :
    Call.initStackFrame (ExecutionMachine.callHooks (ActualReferenceContext.config s.options (s.remaining+1) s.span) s.limits) ()
      HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody HelperCompilerFacts.asMutPtrAbi
      #[.Copy ⟨.immediate (parent s),ActualReferenceMetadata.reference⟩] false (destination s) (.goto (some 7) .Continue) (initial s)=
      .ok () (Storage.withCurrent #[caller s] (helper s) (after s)) := by
  have a:=accounted_fields s
  have valid : (15 : MIR.LocalId)<(caller s).locals.size := by simpa [caller,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout] using s.valid15
  have live : (caller s).locals[15].value=.live (.immediate .uninit) := by simpa [caller,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout] using s.live15
  have cached : (caller s).locals[15].layout=some CopyCompilerFacts.destPointerLayout := by simp [caller,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout]
  have active : (accounted s).threads.activeThread?=some s.thread := by rw [a.threads];exact s.active
  have top : FrameRelevance.top (AsMutPush.pushed s.options.userRelevantCrates (initial s) (destination s)).stack s.thread.topUserRelevantFrame=some 0 := by
    simp [FrameRelevance.top,s.top]
  have current : (AsMutPush.pushed s.options.userRelevantCrates (initial s) (destination s)).stack.frames[0]?=some (caller s) := by
    simp [AsMutPush.pushed,initial,Storage.withCurrent]
  have call:=GeneralBorrowExposedScopedInactiveWritableAsMutEntry.actual_entry s.options s.limits s.remaining s.span s.ctx s.debug s.cmp
    s.dynamicFuel s.fuel s.dynamic s.validation s.id s.entry s.base s.offset s.len s.parentTag s.positive s.nonzero s.signedFits s.bounds
    #[] (caller s) (accounted s) s.tracker a.tracked s.mode s.fresh s.selected s.head s.tail s.data s.capacity 15 valid .uninit live cached s.clocks
    (by change (AsMutPtrReturn.accountedMachine s.options s.remaining s.span s.machine).user.payload.ghost=false;rw [AsMutPtrReturn.accounted_ghost];exact s.ghost) (by change (AsMutPtrReturn.accountedMachine s.options s.remaining s.span s.machine).user.payload.validation=.Shallow;rw [AsMutPtrReturn.accounted_validation];exact s.shallow)
    (by rw [a.addresses];exact s.cachedAddress) (by rw [a.memory];exact s.present) a.race
    (by change (accounted s).user.payload.payload.user.types.metadata=_;rw [a.types];exact s.metadata)
    (by change (accounted s).user.payload.payload.user.types.entries.any (·.value.ty==4)=false;rw [a.types];exact s.notConstructed)
    s.thread 0 (caller s) active top current
  exact call

theorem source_step {profileMode : ProfileMode} (s : InputFor profileMode) :
    ExecutionMachine.step (ActualReferenceContext.config s.options (s.remaining+1) s.span) s.limits ()
      (Storage.withCurrent #[] s.caller s.machine)=(Storage.withCurrent #[caller s] (helper s) (after s),.ok true) := by
  let cfg:=ActualReferenceContext.config s.options (s.remaining+1) s.span
  let initial:=Storage.withCurrent #[] s.caller s.machine
  let next:=Storage.withCurrent #[] s.caller (accounted s)
  let final:=Storage.withCurrent #[caller s] (helper s) (after s)
  have a:=accounted_fields s
  have call:=GenericAsMutCallFrontend.call_uncached s.options s.limits s.remaining s.budget s.dispatch s.span s.debug s.source s.cmp
    s.caller (helper s) (accounted s) (after s) (parent s) s.body s.identity s.callee s.location s.valid16 s.live16 s.cached16 s.valid15 .uninit
    s.live15 s.uncached15 s.clocks (by change (AsMutPtrReturn.accountedMachine s.options s.remaining s.span s.machine).user.payload.ghost=false;rw [AsMutPtrReturn.accounted_ghost];exact s.ghost)
    (by exact a.backend) a.race (actual_entry s)
  have accounting:=SourceControl.before_terminator cfg s.limits () initial
    (CanonicalConfigFacts.actual_term_get_set s.options () (s.remaining+1) s.span)
    (CanonicalConfigFacts.actual_term_set_set s.options () (s.remaining+1) s.span) s.unchecked s.noGc s.fixed
  let block:=RootBody.reflected.body.body.basicBlocks[6]'(by decide +kernel)
  have blockAt : s.caller.body.basicBlocks[6]?=some block := by rw [s.body];simp [block]
  have noStatement : block.statements[8]?=none := by with_unfolding_all rfl
  apply GenericCallStages.source_step cfg s.limits () initial next final s.caller ⟨6,8⟩ block
    HelperCompilerFacts.asMutPtrCall.function #[AsMutEvaluateCall.argument] ⟨15,#[]⟩ (some 7) .Continue
    AsMutCallTerminator.sourceKind AsMutCallTerminator.fnSpan
    (by simp [initial,Storage.withCurrent,Stack.currentFrame?]) s.location blockAt noStatement AsMutCallTerminator.source_call accounting call
  change 2≠1
  decide
end
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableAsMutCallState
