import duplicate_prefix.GeneralBorrowExposedScopedAsMutCallState
import duplicate_prefix.GeneralBorrowExposedScopedAsMutRawReleaseData
namespace DuplicatePrefix.GeneralBorrowExposedScopedAsMutCallReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open GeneralBorrowExposedScopedAsMutCallInput
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

def pointer (s : Input) : Pointer Provenance := Pointer.new (.concrete s.id s.tracker.global.nextPointerTag) (Size.ofBytes (s.base+s.offset))
def released (s : Input) := ((childTree s).releaseProtector s.tracker.global.nextPointerTag (held s).global.protectedTags).tree

theorem after_flags (s : Input) :
    ((ActualReferenceContext.config s.options (s.remaining+1) s.span).terminators.getControl (after s).user).checkedArithmetic=false ∧
    ((ActualReferenceContext.config s.options (s.remaining+1) s.span).terminators.getControl (after s).user).gcInterval=0 := by
  have p:=GeneralBorrowExposedScopedAsMutCallState.pushed_fields s
  have control : (ActualReferenceContext.config s.options (s.remaining+1) s.span).terminators.getControl (after s).user =
      (ActualReferenceContext.config s.options (s.remaining+1) s.span).terminators.getControl (accounted s).user := by
    rw [(CanonicalConfigFacts.actual_fields s.options () (s.remaining+1) s.span).terminators]
    change (pushed s).user.payload.payload.user.host.control=(accounted s).user.payload.payload.user.host.control
    rw [p.user]
  rw [control]
  exact ⟨(RootZeroCompleteState.tick_flags s.options s.remaining s.span s.machine).1.trans s.unchecked,
    (RootZeroCompleteState.tick_flags s.options s.remaining s.span s.machine).2.trans s.noGc⟩

theorem executes (s : Input) :
    let cfg:=ActualReferenceContext.config s.options (s.remaining+1) s.span
    ∃ root post,
      SuccessfulTrace.Trace cfg s.limits (Storage.withCurrent #[] s.caller s.machine) (Storage.withCurrent #[] root post) ∧
      root={AsMutPtrReturn.writeFrame (caller s) 15 (.scalar (Scalar.fromPointer cfg.access.runtime.base (pointer s)))
        (by simpa [caller,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout] using s.valid15) with location:=.mir ⟨7,0⟩} ∧
      post.memory=RetagEntry.updatedMemory s.machine.memory s.id s.entry (released s) ∧
      post.borrowTracker=some {held s with global:=(held s).global.endCall (({} : FrameState).addProtector s.id s.tracker.global.nextPointerTag)} ∧
      ((childTree s).releaseProtector s.tracker.global.nextPointerTag (held s).global.protectedTags).status=.Released ∧
      GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span s.machine post := by
  have a:=GeneralBorrowExposedScopedAsMutCallState.accounted_fields s
  have p:=GeneralBorrowExposedScopedAsMutCallState.pushed_fields s
  have flags:=after_flags s
  let releaseData:=GeneralBorrowExposedScopedAsMutRawReleaseData.build s.entry.allocation.extra s.tracker s.parentTag s.offset s.len
    s.selected s.head s.tail s.data s.atBase s.full s.rangePositive s.clean
  have valid : (15 : MIR.LocalId)<(caller s).locals.size := by simpa [caller,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout] using s.valid15
  have live : (caller s).locals[15].value=.live (.immediate .uninit) := by simpa [caller,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout] using s.live15
  have cached : (caller s).locals[15].layout=some CopyCompilerFacts.destPointerLayout := by simp [caller,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout]
  have present : (after s).memory.live.find? (fun row=>row.1==s.id)=some (s.id,inside s) := by
    exact StackPopRelease.lookup_commit_same (pushed s).memory s.id s.entry (childTree s)
  have address : (after s).user.addresses.baseAddr.find? (fun row=>row.allocId==s.id)=some ⟨s.id,s.base⟩ := by
    change (pushed s).user.addresses.baseAddr.find? _=_
    rw [p.addresses]
    exact s.cachedAddress
  let thread:=PushThread.after s.thread 1 (AsMutFrame.rank s.options.userRelevantCrates) (caller s).extra.userRelevance
  obtain ⟨done,body,extra⟩ := GeneralBorrowExposedScopedAsMutInitializedComplete.run s.options s.limits s.remaining s.span s.debug
    s.fuel s.validation s.dynamicFuel s.dynamic s.cmp #[] (caller s) (initial s) a.race (parent s) (after s) s.tracker.global.nextPointerTag
    s.id (inside s) s.base s.offset s.len present s.positive s.nonzero s.signedFits s.bounds address (held s) rfl s.mode releaseData
    p.ghost p.shallow 15 valid live cached s.clocks
    (by change (pushed s).user.payload.payload.user.types.metadata=_;rw [p.types];exact s.metadata)
    (by change (pushed s).user.payload.payload.user.types.entries.any (·.value.ty==4)=false;rw [p.types];exact s.notConstructed)
    thread p.active flags.1 flags.2 p.fixed
  let memory:=StackPopRelease.commitTree (after s).memory s.id (inside s) (released s)
  let post:=GenericAsMutReturnState.machine s.options s.remaining s.span #[] (caller s) done (after s) memory (held s)
    (({} : FrameState).addProtector s.id s.tracker.global.nextPointerTag) thread
  let root : CompilerFrameContext.ActualFrame :=
    {AsMutPtrReturn.writeFrame (caller s) 15 (.scalar (Scalar.fromPointer
      (ActualReferenceContext.config s.options (s.remaining+1) s.span).access.runtime.base (pointer s))) valid with location:=.mir ⟨7,0⟩}
  have trace : SuccessfulTrace.Trace (ActualReferenceContext.config s.options (s.remaining+1) s.span) s.limits
      (Storage.withCurrent #[caller s] (helper s) (after s)) (Storage.withCurrent #[] root post) := body
  rcases GenericAsMutReturnState.fields s.options s.remaining s.span #[] (caller s) done (after s) memory (held s)
      (({} : FrameState).addProtector s.id s.tracker.global.nextPointerTag) thread with
    ⟨postMemory,postTracked,postRace,postFixed,postAddresses,postGhost,postShallow,postTypes,postBackend,postExtras⟩
  have memoryFinal : memory=RetagEntry.updatedMemory s.machine.memory s.id s.entry (released s) := by
    change RetagEntry.updatedMemory (RetagEntry.updatedMemory (pushed s).memory s.id s.entry (childTree s)) s.id (inside s) (released s)=_
    rw [p.memory]
    exact RetagEntry.updated_memory_twice s.machine.memory s.id s.entry (childTree s) (released s)
  have control : (ActualReferenceContext.config s.options (s.remaining+1) s.span).terminators.getControl post.user=
      TerminatorClock.advance ((ActualReferenceContext.config s.options (s.remaining+1) s.span).terminators.getControl (after s).user) :=
    GenericAsMutReturnState.control s.options s.remaining s.span #[] (caller s) done (after s) memory (held s)
      (({} : FrameState).addProtector s.id s.tracker.global.nextPointerTag) thread
  have runtime : GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span s.machine post := by
    refine ⟨postGhost.trans p.ghost,postShallow.trans p.shallow,postRace.trans p.race,
      postAddresses.trans p.addresses,postTypes.trans p.types,postExtras.trans p.extras,postBackend.trans p.backend,?_,?_,postFixed.trans p.fixed,?_⟩
    · rw [control];exact flags.1
    · rw [control];exact flags.2
    · exact ⟨s.thread,GenericAsMutReturnState.active s.options s.remaining s.span (caller s) done (after s) memory (held s)
        (({} : FrameState).addProtector s.id s.tracker.global.nextPointerTag) s.thread (AsMutFrame.rank s.options.userRelevantCrates)
        (caller s).extra.userRelevance p.active s.top,s.top⟩
  have releaseDone:=GeneralBorrowExposedScopedAsMutReleasePlan.released (childTree s) (held s).global.protectedTags s.tracker.global.nextPointerTag releaseData
  exact ⟨root,post,SuccessfulTrace.Trace.next (GeneralBorrowExposedScopedAsMutCallState.source_step s) trace,rfl,
    postMemory.trans memoryFinal,postTracked,releaseDone,runtime⟩
end
end DuplicatePrefix.GeneralBorrowExposedScopedAsMutCallReturn
