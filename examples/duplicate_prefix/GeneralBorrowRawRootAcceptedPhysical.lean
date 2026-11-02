import duplicate_prefix.GeneralBorrowRawRootToLenBoth
import duplicate_prefix.GeneralBorrowRawRootLenCaller
import duplicate_prefix.GeneralBorrowRawRootTickRuntime
import duplicate_prefix.GeneralBorrowRawLenAcceptedFrame
namespace DuplicatePrefix.GeneralBorrowRawRootAcceptedPhysical
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GenericFunctionEntryState
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
abbrev Initial := GeneralBorrowRawRootZeroEntry.Initial

structure Heap (s : Initial) (initial post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) where
  tree : BorrowTree
  tracker : MachineHooks.BorrowState
  child : UniIndex
  memory : post.memory = RetagEntry.updatedMemory initial.memory s.id s.entry tree
  tracked : post.borrowTracker = some tracker
  mode : tracker.retagMode = .Default
  formed : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global
  owner : Nonempty (GeneralBorrowReadRowRange.Positive tree tracker.global.protectedTags child s.raw.selected s.raw.maximum s.offset s.len)
  observer : UniIndex
  original : Nonempty (DuplicatePrefixBorrowAuthorization.Positive tree tracker.global.protectedTags
    (some observer) (some s.raw.selected) s.raw.maximum s.offset s.len)
  originalActivity : GeneralBorrowFreshActiveWithin.ActiveWithin tree observer .Write s.offset (s.offset+s.len)
  runtime : GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span s.before post

structure Frame (entry result : CompilerFrameContext.ActualFrame) : Prop where
  body : result.body = RootBody.reflected.body.body
  identity : result.bodyIdentity = RootBody.reflected.body.identity
  callee : result.functionInstance = RootBody.reflected.functionInstance
  extra : result.extra = entry.extra
  returnPlace : result.returnPlace = entry.returnPlace
  continuation : result.returnContinuation = entry.returnContinuation
  varargs : result.vaList = entry.vaList
  localsIdentity : result.localsIdentity = entry.localsIdentity
  track : result.trackCallerArg = entry.trackCallerArg
  size : result.locals.size = 25
  location : result.location = .mir ⟨6,7⟩
  source : result.locals[1]? = entry.locals[1]?
  count : result.locals[2]? = entry.locals[2]?
  flag : result.locals[13]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩
  temp15 : result.locals[15]? = some ⟨.live (.immediate .uninit),none⟩
  temp16 : result.locals[16]? = some ⟨.live (.immediate .uninit),none⟩
  high : ∀ index, 17 ≤ index → result.locals[index]? = entry.locals[index]?
  immediate : CopyHelperCleanup.AllImmediate result
  zero : result.locals[0]? = some ⟨.live (.immediate .uninit),none⟩

private theorem cell (frame : CompilerFrameContext.ActualFrame) (i : Nat) (valid : i < frame.locals.size)
    (row : LocalState Provenance LocalLayout) (present : frame.locals[i]? = some row) : frame.locals[i] = row :=
  Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans present)

/-- The accepted count branch from original call-time data. Initialization,
shared Ref, len, release/return and pure accepted guard are all actual traces. -/
theorem executes (s : Initial) (n : UInt64) (positiveCount : n ≠ 0) (within : n ≤ s.len/2)
    (preciseOff : s.options.retag.preciseInteriorMut = false)
    (implicitOff : s.options.retag.implicitWrites = false)
    (budget : Nat) (dispatch : s.limits.callDispatch = budget+1)
    (nodeMargin : s.entry.allocation.extra.nodes.size+3 < 65536)
    (tagMargin : s.tracker.global.nextPointerTag.value.toNat+3 < 18446744073709551615) :
    ∃ (entryFrame result : CompilerFrameContext.ActualFrame)
      (initial post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      GeneralBorrowRawRootPositivePrefix.ActualCall s n entryFrame initial ∧
      entryFrame = GeneralBorrowRawRootInitialize.caller s n ∧
      SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits (Storage.withCurrent #[] entryFrame initial)
        (Storage.withCurrent #[] result post) ∧ Frame entryFrame result ∧ Nonempty (Heap s initial post) := by
  obtain ⟨entryFrame,callerFrame,returned,initial,machine,call,entryEq,trace,shape,⟨outcome⟩⟩ :=
    GeneralBorrowRawRootToLenBoth.executes s n positiveCount preciseOff implicitOff budget dispatch nodeMargin tagMargin
  let caller := GeneralBorrowRawRootLenCaller.caller s callerFrame shape.size
  have facts := GeneralBorrowRawRootLenCaller.of_shape s n entryFrame callerFrame entryEq shape
  have bounded (i : Fin 25) : i.val < caller.locals.size := by rw [facts.size];exact i.isLt
  have zero := cell caller 0 (bounded ⟨0,by decide⟩) _ facts.zero
  have seven := cell caller 7 (bounded ⟨7,by decide⟩) _ facts.seven
  have eight := cell caller 8 (bounded ⟨8,by decide⟩) _ facts.eight
  have nine := cell caller 9 (bounded ⟨9,by decide⟩) _ facts.nine
  have ten := cell caller 10 (bounded ⟨10,by decide⟩) _ facts.ten
  have twelve := cell caller 12 (bounded ⟨12,by decide⟩) _ facts.twelve
  have thirteen := cell caller 13 (bounded ⟨13,by decide⟩) _ facts.thirteen
  have fifteen := cell caller 15 (bounded ⟨15,by decide⟩) _ facts.fifteen
  have sixteen := cell caller 16 (bounded ⟨16,by decide⟩) _ facts.sixteen
  obtain ⟨result,data,frameFacts⟩ := GeneralBorrowRawLenAcceptedFrame.executes s.options s.limits s.remaining s.span s.source
    s.debugOff s.validityFuel s.validationEq caller machine s.len n (UInt64.pos_iff_ne_zero.mpr positiveCount) within facts.size
    (GeneralBorrowRawRootToLen.refValue s) (congrArg LocalState.value twelve)
    (congrArg LocalState.value thirteen) (congrArg LocalState.layout thirteen)
    (congrArg LocalState.value zero) (congrArg LocalState.layout zero)
    (congrArg LocalState.value seven) (congrArg LocalState.layout seven)
    (congrArg LocalState.value fifteen) (congrArg LocalState.layout fifteen)
    (congrArg LocalState.value sixteen) (congrArg LocalState.layout sixteen)
    (congrArg LocalState.value eight) (congrArg LocalState.layout eight)
    (congrArg LocalState.value nine) (congrArg LocalState.layout nine)
    (congrArg LocalState.value ten) (congrArg LocalState.layout ten)
    facts.body facts.identity facts.callee facts.immediate facts.clocks outcome.tracker outcome.tracked outcome.mode
    outcome.runtime.ghost outcome.runtime.shallow outcome.runtime.unchecked outcome.runtime.noGc outcome.runtime.fixed
  obtain ⟨guardTrace,bodyAfter,identityAfter,calleeAfter,extraAfter,placeAfter,continuationAfter,varargsAfter,localsIdentityAfter,
    trackAfter,sizeAfter,locationAfter,slot1,slot2,slot15,slot16,allAfter⟩ := data
  have attributes := LenCallResultFrame.attributes caller (bounded ⟨11,by decide⟩) s.len
  let post := RootZeroCompleteState.tick s.options s.remaining s.span (RootZeroCompleteState.tick s.options s.remaining s.span machine)
  have ledger := GeneralBorrowRawLenAcceptedFrame.machine_ledger s.options s.remaining s.span machine
  have runtime := GeneralBorrowRawRootTickRuntime.preserves s _ (GeneralBorrowRawRootTickRuntime.preserves s machine outcome.runtime)
  have finalTrace : SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits
      (Storage.withCurrent #[] returned machine) (Storage.withCurrent #[] result post) := by
    simpa only [outcome.frameEq,GeneralBorrowRawRootToLenBoth.lenFrame,GeneralBorrowRawRootLenCaller.caller,caller,post,GeneralBorrowRawRootToLenBoth.refValue,GeneralBorrowRawRootToLen.refValue] using guardTrace
  refine ⟨entryFrame,result,initial,post,call,entryEq,SuccessfulTrace.append trace finalTrace,?_,?_⟩
  · refine ⟨bodyAfter.trans (attributes.1.trans facts.body),identityAfter.trans (attributes.2.1.trans facts.identity),
      calleeAfter.trans (attributes.2.2.1.trans facts.callee),extraAfter.trans (attributes.2.2.2.1.trans facts.extra),
      placeAfter.trans (attributes.2.2.2.2.2.1.trans facts.returnPlace),
      continuationAfter.trans (attributes.2.2.2.2.2.2.1.trans facts.continuation),
      varargsAfter.trans (attributes.2.2.2.2.2.2.2.2.1.trans facts.varargs),
      localsIdentityAfter.trans (attributes.2.2.2.2.1.trans facts.localsIdentity),
      trackAfter.trans (attributes.2.2.2.2.2.2.2.1.trans facts.track),sizeAfter,locationAfter,?_,?_,frameFacts.slot13,slot15,slot16,?_,allAfter,?_⟩
    · exact slot1.trans ((LenCallResultFrame.other caller (bounded ⟨11,by decide⟩) s.len 1 (by decide)).trans facts.source)
    · exact slot2.trans ((LenCallResultFrame.other caller (bounded ⟨11,by decide⟩) s.len 2 (by decide)).trans facts.count)
    · intro index high
      exact (frameFacts.high index high).trans ((LenCallResultFrame.other caller (bounded ⟨11,by decide⟩) s.len index (by omega)).trans (facts.high index high))
    · exact frameFacts.slot0.trans ((LenCallResultFrame.other caller (bounded ⟨11,by decide⟩) s.len 0 (by decide)).trans facts.zero)
  · exact ⟨{
      tree:=outcome.tree,tracker:=outcome.tracker,child:=outcome.child,memory:=ledger.1.trans outcome.memory,
      tracked:=ledger.2.1.trans outcome.tracked,mode:=outcome.mode,formed:=outcome.formed,owner:=outcome.owner,observer:=outcome.observer,
      original:=outcome.original,originalActivity:=outcome.originalActivity,runtime:=runtime}⟩
/-- Concrete accepted caller fields, derived from original installation and
actual accepted-prefix frame ledger. -/
structure PhysicalFacts (s : Initial) (n : UInt64) (frame : CompilerFrameContext.ActualFrame) : Prop where
  clocks : frame.extra.dataRace = none
  track : frame.trackCallerArg = none
  relevant : frame.extra.userRelevance > 0
  continuation : frame.returnContinuation = .stop true
  varargs : frame.vaList = #[]
  destination : frame.returnPlace = .memory s.place
  source : frame.locals[1]? = some ⟨.live (.immediate (GeneralBorrowRawRootPrefixFrame.sourceValue s)),some ActualReferenceMetadata.reference⟩
  count : frame.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩
  high : ∀ index,17 ≤ index → index ≤ 24 → frame.locals[index]? = some ⟨.dead,none⟩
  tracked : frame.extra.borrowTracker = some ((({} : FrameState).addProtector s.id s.tracker.global.nextPointerTag).addProtector s.slotId
    (next s.tracker s.fresh).global.nextPointerTag)

theorem physical (s : Initial) (n : UInt64) (entry frame : CompilerFrameContext.ActualFrame)
    (initial : entry = GeneralBorrowRawRootInitialize.caller s n) (facts : Frame entry frame) :
    PhysicalFacts s n frame := by
  let raw := RawRootInvocation.root s.before s.place s.race
  let value := GeneralBorrowRawRootPrefixFrame.sourceValue s
  let tag := (next s.tracker s.fresh).global.nextPointerTag
  have metadata := PositiveRootInstalledFrame.metadata raw value n {} s.id s.tracker.global.nextPointerTag s.slotId tag
  have slots (i : Fin 25) := PositiveRootInstalledFrame.slot_option raw
    (RawRootInvocation.locals s.before s.place s.race) value n {} s.id s.tracker.global.nextPointerTag s.slotId tag i
  have fixed : entry = PositiveRootInstalledFrame.installed raw value n {} s.id s.tracker.global.nextPointerTag s.slotId tag := initial
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [facts.extra,fixed,metadata.2.2.2.2.2.2.1];exact raw.noClocks
  · rw [facts.track,fixed,PositiveRootInstalledFrame.track];exact (RawRootInvocation.control s.before s.place s.race).2.1
  · rw [facts.extra,fixed]
    rw [PositiveRootInstalledFrame.relevance,PositiveRootInstalledFrame.raw_relevance];decide
  · rw [facts.continuation,fixed,metadata.2.2.2.1];exact (RawRootInvocation.control s.before s.place s.race).2.2.1
  · rw [facts.varargs,fixed,metadata.2.2.2.2.2.1];rfl
  · rw [facts.returnPlace,fixed,metadata.2.2.2.2.1];exact (RawRootInvocation.control s.before s.place s.race).2.2.2
  · rw [facts.source,fixed]
    simpa only [Nat.reduceEqDiff,or_self,ite_false,ite_true,value] using slots ⟨1,by decide⟩
  · rw [facts.count,fixed]
    simpa only [Nat.reduceEqDiff,or_self,ite_false,ite_true] using slots ⟨2,by decide⟩
  · intro index low high
    rw [facts.high index low,fixed]
    have bound : index < 25 := by omega
    have n14 : ¬14=index := by omega
    have n13 : ¬13=index := by omega
    have n6 : ¬6=index := by omega
    have n0 : ¬0=index := by omega
    have n2 : ¬2=index := by omega
    have n1 : ¬1=index := by omega
    simpa only [n14,n13,n6,n0,n2,n1,false_or,ite_false] using slots ⟨index,bound⟩
  · rw [facts.extra,fixed]
    exact metadata.2.2.2.2.2.2.2.1

end
end DuplicatePrefix.GeneralBorrowRawRootAcceptedPhysical
