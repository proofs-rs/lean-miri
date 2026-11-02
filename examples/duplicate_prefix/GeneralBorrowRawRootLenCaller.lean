import duplicate_prefix.GeneralBorrowRawRootToLen
namespace DuplicatePrefix.GeneralBorrowRawRootLenCaller
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GenericFunctionEntryState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
abbrev Initial := GeneralBorrowRawRootZeroEntry.Initial

def caller (s : Initial) (frame : CompilerFrameContext.ActualFrame) (size : frame.locals.size = 25) : CompilerFrameContext.ActualFrame :=
  GeneralBorrowForestSharedPreLenFrame.after frame (by rw [size];decide) (GeneralBorrowRawRootToLen.refValue s)

structure Facts (s : Initial) (n : UInt64) (entry frame : CompilerFrameContext.ActualFrame) : Prop where
  size : frame.locals.size = 25
  body : frame.body = RootBody.reflected.body.body
  identity : frame.bodyIdentity = RootBody.reflected.body.identity
  callee : frame.functionInstance = RootBody.reflected.functionInstance
  clocks : frame.extra.dataRace = none
  extra : frame.extra = entry.extra
  returnPlace : frame.returnPlace = entry.returnPlace
  continuation : frame.returnContinuation = entry.returnContinuation
  varargs : frame.vaList = entry.vaList
  localsIdentity : frame.localsIdentity = entry.localsIdentity
  track : frame.trackCallerArg = entry.trackCallerArg
  immediate : CopyHelperCleanup.AllImmediate frame
  source : frame.locals[1]? = entry.locals[1]?
  count : frame.locals[2]? = entry.locals[2]?
  zero : frame.locals[0]? = some ⟨.live (.immediate .uninit),none⟩
  seven : frame.locals[7]? = some ⟨.live (.immediate .uninit),none⟩
  eight : frame.locals[8]? = some ⟨.live (.immediate .uninit),none⟩
  nine : frame.locals[9]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩
  ten : frame.locals[10]? = some ⟨.live (.immediate .uninit),none⟩
  twelve : frame.locals[12]? = some ⟨.live (.immediate (GeneralBorrowRawRootToLen.refValue s)),some SharedReferenceMetadata.sharedLayout⟩
  thirteen : frame.locals[13]? = some ⟨.live (.immediate .uninit),none⟩
  fifteen : frame.locals[15]? = some ⟨.dead,none⟩
  sixteen : frame.locals[16]? = some ⟨.dead,none⟩
  high : ∀ index, 17 ≤ index → frame.locals[index]? = entry.locals[index]?

theorem of_shape (s : Initial) (n : UInt64) (entry frame : CompilerFrameContext.ActualFrame)
    (initial : entry = GeneralBorrowRawRootInitialize.caller s n)
    (shape : GenericFunctionEntryPrefix.Shape entry frame n) :
    Facts s n entry (caller s frame shape.size) := by
  have prefixFacts := GeneralBorrowRawRootPrefixFrame.of_shape s n entry frame initial shape
  let after := caller s frame shape.size
  have kept (index : Nat) (different : index ≠ 12) : after.locals[index]? = frame.locals[index]? := by
    simp [after,caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,ActualLocalCopy.written,
      LocalPlaces.cachePlaceLayout,Array.getElem?_set,different,Ne.symm different]
  have metadata : after.body = frame.body ∧ after.bodyIdentity = frame.bodyIdentity ∧
      after.functionInstance = frame.functionInstance ∧ after.extra = frame.extra ∧
      after.returnPlace = frame.returnPlace ∧ after.returnContinuation = frame.returnContinuation ∧
      after.vaList = frame.vaList ∧ after.localsIdentity = frame.localsIdentity ∧ after.trackCallerArg = frame.trackCallerArg := by
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  have original (i : Fin 25) := PositiveRootInstalledFrame.slot_option (RawRootInvocation.root s.before s.place s.race)
    (RawRootInvocation.locals s.before s.place s.race) (GeneralBorrowRawRootPrefixFrame.sourceValue s) n {} s.id s.tracker.global.nextPointerTag
    s.slotId (next s.tracker s.fresh).global.nextPointerTag i
  have entry0 : entry.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ := by
    rw [initial]
    simpa only [GeneralBorrowRawRootInitialize.caller,GeneralBorrowRawRootPrefixFrame.sourceValue,Nat.reduceEqDiff,or_self,or_true,true_or,false_or,or_false,eq_self_iff_true,ite_false,ite_true] using original ⟨0,by decide⟩
  have entry13 : entry.locals[13]? = some ⟨.live (.immediate .uninit),none⟩ := by
    rw [initial]
    simpa only [GeneralBorrowRawRootInitialize.caller,GeneralBorrowRawRootPrefixFrame.sourceValue,Nat.reduceEqDiff,or_self,or_true,true_or,false_or,or_false,eq_self_iff_true,ite_false,ite_true] using original ⟨13,by decide⟩
  have entry15 : entry.locals[15]? = some ⟨.dead,none⟩ := by
    rw [initial]
    simpa only [GeneralBorrowRawRootInitialize.caller,GeneralBorrowRawRootPrefixFrame.sourceValue,Nat.reduceEqDiff,or_self,or_true,true_or,false_or,or_false,eq_self_iff_true,ite_false,ite_true] using original ⟨15,by decide⟩
  have entry16 : entry.locals[16]? = some ⟨.dead,none⟩ := by
    rw [initial]
    simpa only [GeneralBorrowRawRootInitialize.caller,GeneralBorrowRawRootPrefixFrame.sourceValue,Nat.reduceEqDiff,or_self,or_true,true_or,false_or,or_false,eq_self_iff_true,ite_false,ite_true] using original ⟨16,by decide⟩
  refine ⟨?_,metadata.1.trans prefixFacts.body,metadata.2.1.trans prefixFacts.identity,metadata.2.2.1.trans prefixFacts.callee,
    ?_,metadata.2.2.2.1.trans shape.extra,metadata.2.2.2.2.1.trans shape.returnPlace,
    metadata.2.2.2.2.2.1.trans shape.continuation,metadata.2.2.2.2.2.2.1.trans shape.vaList,
    metadata.2.2.2.2.2.2.2.1.trans shape.localsIdentity,metadata.2.2.2.2.2.2.2.2.trans shape.track,
    ?_,(kept 1 (by decide)).trans shape.slot1,(kept 2 (by decide)).trans shape.slot2,
    (kept 0 (by decide)).trans (shape.slot0.trans entry0),
    (kept 7 (by decide)).trans shape.slot7,(kept 8 (by decide)).trans shape.slot8,
    (kept 9 (by decide)).trans shape.slot9,(kept 10 (by decide)).trans shape.slot10,?_,
    (kept 13 (by decide)).trans ((shape.keep 13 (by decide)).trans entry13),
    (kept 15 (by decide)).trans ((shape.keep 15 (by decide)).trans entry15),
    (kept 16 (by decide)).trans ((shape.keep 16 (by decide)).trans entry16),?_⟩
  · simpa [after,caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using shape.size
  · rw [metadata.2.2.2.1];exact prefixFacts.clocks
  · exact CopyHelperCleanup.all_immediate_written frame 12 SharedReferenceMetadata.sharedLayout (GeneralBorrowRawRootToLen.refValue s)
      (by rw [shape.size];decide) shape.immediate
  · simp [after,caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout]
  · intro index lower
    exact (kept index (by omega)).trans (shape.keep index (by omega))
end
end DuplicatePrefix.GeneralBorrowRawRootLenCaller
