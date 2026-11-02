import duplicate_prefix.GeneralBorrowRawWildcardWindowInitial
import duplicate_prefix.GenericFunctionEntryPrefix
namespace DuplicatePrefix.GeneralBorrowRawWildcardWindowPrefixFacts
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open GeneralBorrowRawWildcardWindowInitial
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
structure Facts (s : Initial) (n : UInt64) (frame : CompilerFrameContext.ActualFrame) : Prop where
  clocks : frame.extra.dataRace = none
  track : frame.trackCallerArg = none
  relevant : frame.extra.userRelevance > 0
  continuation : frame.returnContinuation = .stop true
  varargs : frame.vaList = #[]
  destination : frame.returnPlace = .memory s.place
  tracked : frame.extra.borrowTracker = some ((({} : FrameState).addProtector s.id s.tracker.global.nextPointerTag).addProtector s.slotId
    (GeneralBorrowRawWildcardWindowFunctionState.next s.tracker s.fresh).global.nextPointerTag)
  zero : frame.locals[0]? = some ⟨.live (.immediate .uninit),none⟩
  thirteen : frame.locals[13]? = some ⟨.live (.immediate .uninit),none⟩
  fifteen : frame.locals[15]? = some ⟨.dead,none⟩
  sixteen : frame.locals[16]? = some ⟨.dead,none⟩
  high : ∀ index,17 ≤ index → index ≤ 24 → frame.locals[index]? = some ⟨.dead,none⟩

theorem of_shape (s : Initial) (n : UInt64) (frame : CompilerFrameContext.ActualFrame)
    (shape : GenericFunctionEntryPrefix.Shape (caller s n) frame n) : Facts s n frame := by
  let raw := RawRootInvocation.root s.before s.place s.race
  let tag := (GeneralBorrowRawWildcardWindowFunctionState.next s.tracker s.fresh).global.nextPointerTag
  have metadata := PositiveRootInstalledFrame.metadata raw (adjusted s) n {} s.id s.tracker.global.nextPointerTag s.slotId tag
  have slots (i : Fin 25) := PositiveRootInstalledFrame.slot_option raw
    (RawRootInvocation.locals s.before s.place s.race) (adjusted s) n {} s.id s.tracker.global.nextPointerTag s.slotId tag i
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [shape.extra]
    change (PositiveRootInstalledFrame.installed raw _ _ _ _ _ _ _).extra.dataRace = none
    rw [metadata.2.2.2.2.2.2.1];exact raw.noClocks
  · rw [shape.track]
    change (PositiveRootInstalledFrame.installed raw _ _ _ _ _ _ _).trackCallerArg = none
    rw [PositiveRootInstalledFrame.track];exact (RawRootInvocation.control s.before s.place s.race).2.1
  · rw [shape.extra]
    change (PositiveRootInstalledFrame.installed raw _ _ _ _ _ _ _).extra.userRelevance > 0
    rw [PositiveRootInstalledFrame.relevance,PositiveRootInstalledFrame.raw_relevance];decide
  · rw [shape.continuation]
    change (PositiveRootInstalledFrame.installed raw _ _ _ _ _ _ _).returnContinuation = .stop true
    rw [metadata.2.2.2.1];exact (RawRootInvocation.control s.before s.place s.race).2.2.1
  · rw [shape.vaList]
    change (PositiveRootInstalledFrame.installed raw _ _ _ _ _ _ _).vaList = #[]
    rw [metadata.2.2.2.2.2.1];rfl
  · rw [shape.returnPlace]
    change (PositiveRootInstalledFrame.installed raw _ _ _ _ _ _ _).returnPlace = .memory s.place
    rw [metadata.2.2.2.2.1];exact (RawRootInvocation.control s.before s.place s.race).2.2.2
  · rw [shape.extra]
    exact metadata.2.2.2.2.2.2.2.1
  · rw [shape.slot0]
    simpa only [caller,Nat.reduceEqDiff,or_self,or_true,true_or,ite_false,ite_true] using slots ⟨0,by decide⟩
  · rw [shape.keep 13 (by decide)]
    simpa only [caller,Nat.reduceEqDiff,or_self,or_true,true_or,ite_false,ite_true] using slots ⟨13,by decide⟩
  · rw [shape.keep 15 (by decide)]
    simpa only [caller,Nat.reduceEqDiff,or_self,or_true,true_or,ite_false,ite_true] using slots ⟨15,by decide⟩
  · rw [shape.keep 16 (by decide)]
    simpa only [caller,Nat.reduceEqDiff,or_self,or_true,true_or,ite_false,ite_true] using slots ⟨16,by decide⟩
  · intro index low high
    rw [shape.keep index (by omega)]
    have bound : index < 25 := by omega
    have n14 : ¬14=index := by omega
    have n13 : ¬13=index := by omega
    have n6 : ¬6=index := by omega
    have n0 : ¬0=index := by omega
    have n2 : ¬2=index := by omega
    have n1 : ¬1=index := by omega
    simpa only [caller,n14,n13,n6,n0,n2,n1,false_or,ite_false] using slots ⟨index,bound⟩
end
end DuplicatePrefix.GeneralBorrowRawWildcardWindowPrefixFacts
