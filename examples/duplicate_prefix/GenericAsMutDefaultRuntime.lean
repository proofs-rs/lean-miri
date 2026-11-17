import duplicate_prefix.GenericAsMutDefaultFrame
namespace DuplicatePrefix.GenericAsMutDefaultRuntime
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open GeneralRangeMapOrigins GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

def entry (s : GenericAsMutInvocationCore.Input) : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
  {s.entry with allocation := (s.entry.allocation.setExtra
    (GeneralBorrowFreshDefaultSequence.child (GenericAsMutDefaultCore.first s) s.tracker.global.protectedTags).tree)}

def caller (s : GenericAsMutInvocationCore.Input) :=
  CopyHelperSteps.advance (ActualLocalCopy.written s.caller 16 (RootReferenceInfo.layout false)
    (by rw [s.size];decide) (GenericAsMutDefaultCore.value s)) ⟨6,7⟩

theorem locals (s : GenericAsMutInvocationCore.Input) :
    (caller s).locals = s.caller.locals.set 16
      ⟨.live (.immediate (GenericAsMutDefaultCore.value s)),some ActualReferenceMetadata.reference⟩ (by rw [s.size];decide) := by
  simp [caller,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootReferenceInfo.layout]

/-- Runtime/frame transport after the actual default mutable statement.
The tree certificates are supplied by the separate pure constructor builder. -/
def core (s : GenericAsMutInvocationCore.Input)
    (fresh : (ReferenceBorrowDriver.allocatedTracker s.tracker s.fresh).global.nextPointerTag.value < 18446744073709551615)
    (data : GenericAsMutPtrEntryValidity.Data (entry s).allocation.extra s.tracker.global.protectedTags
      s.tracker.global.nextPointerTag (ReferenceBorrowDriver.allocatedTracker s.tracker s.fresh).global.nextPointerTag s.offset s.len)
    (clean : Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshMutableStages.slot_index data.slot) = none)
      (entry s).allocation.extra.locations)
    (capacity : (entry s).allocation.extra.locations.size = s.entry.allocation.extra.locations.size) :
    GenericAsMutInvocationCore.Input := by
  have rows := locals s
  have size : (caller s).locals.size = s.caller.locals.size := by rw [rows,Array.size_set]
  have valid15 : (15 : MIR.LocalId) < (caller s).locals.size := by rw [size];exact s.valid15
  refine {s with
    caller := caller s, machine := GenericAsMutDefaultCore.machine s, entry := entry s
    parentTag := s.tracker.global.nextPointerTag, tracker := ReferenceBorrowDriver.allocatedTracker s.tracker s.fresh
    fresh := fresh, data := data, clean := clean, capacity := capacity.trans s.capacity
    cachedAddress := s.cachedAddress, present := ?_, tracked := rfl, mode := s.mode
    ghost := s.ghost, shallow := s.shallow, race := s.race, backend := s.backend
    valid15 := valid15, live15 := ?_, cached15 := ?_, clocks := s.clocks
    metadata := s.metadata, notConstructed := s.notConstructed, active := s.active
    unchecked := s.unchecked, noGc := s.noGc, fixed := s.fixed
    size := size.trans s.size, body := s.body, identity := s.identity, callee := s.callee, track := s.track
    relevant := s.relevant, immediate := ?_, temp16 := GenericAsMutDefaultCore.value s, live16 := ?_
    slot2 := ?_, slot13 := ?_, unused := ?_ }
  · exact StackPopRelease.lookup_commit_same s.machine.memory s.id s.entry _
  · change ((caller s).locals[15]'valid15).value = _
    simpa only [rows,Array.getElem_set,show ¬ ((16 : Nat) = 15) from by decide,ite_false] using s.live15
  · change ((caller s).locals[15]'valid15).layout = _
    simpa only [rows,Array.getElem_set,show ¬ ((16 : Nat) = 15) from by decide,ite_false] using s.cached15
  · exact GenericAsMutDefaultFrame.all_immediate s.caller 16 (RootReferenceInfo.layout false) _ (GenericAsMutDefaultCore.value s) s.immediate
  · rw [rows]
    simp only [Array.getElem?_set_self,Option.map_some]
  · rw [rows]
    simpa only [Array.getElem?_set,show ¬ ((16 : Nat) = 2) from by decide,ite_false] using s.slot2
  · rw [rows]
    simpa only [Array.getElem?_set,show ¬ ((16 : Nat) = 13) from by decide,ite_false] using s.slot13
  · intro index lower upper
    rw [rows]
    have different : (16 : Nat) ≠ index := by omega
    simpa only [Array.getElem?_set,different,ite_false] using s.unused index lower upper
end
end DuplicatePrefix.GenericAsMutDefaultRuntime
