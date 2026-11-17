import duplicate_prefix.GenericSharedRejectedInput
import duplicate_prefix.ProtectorRoundTrip
namespace DuplicatePrefix.GenericSharedRejectedStages
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 200000
noncomputable section

def one_base (s : GenericSharedRejectedInput.Base) := ReferenceBorrowDriver.allocatedTracker s.tracker s.fresh

def two_base (s : GenericSharedRejectedInput.Base) := ReferenceBorrowDriver.allocatedTracker (one_base s) s.fresh2

def held_base (s : GenericSharedRejectedInput.Base) := TypedBorrowSteps.registeredTracker (two_base s) (one_base s).global.nextPointerTag

def ended_base (s : GenericSharedRejectedInput.Base) :=
  {held_base s with global := (held_base s).global.endCall (({} : FrameState).addProtector s.id (one_base s).global.nextPointerTag)}

def one (s : GenericSharedRejectedInput.Input) := one_base s

def two (s : GenericSharedRejectedInput.Input) := two_base s

def held (s : GenericSharedRejectedInput.Input) := held_base s

def ended (s : GenericSharedRejectedInput.Input) := ended_base s

def second (s : GenericSharedRejectedInput.Input) :=
  (GeneralBorrowFreshSharedNext.next s.entry.allocation.extra s.tracker.global.protectedTags s.target
    s.tracker.global.nextPointerTag (one s).global.nextPointerTag s.offset s.len s.first s.noFree s.room
    s.tagFresh s.protectorFresh s.different s.cleanFuture s.owned).val

def child (s : GenericSharedRejectedInput.Input) :=
  (GeneralBorrowFreshSharedSequence.child (second s) s.tracker.global.protectedTags true).tree

/-- Allocating, registering and ending the len protector changes neither the
next-tag value nor the retag mode inherited from the initial root tracker. -/
theorem ended_fields_base (s : GenericSharedRejectedInput.Base) :
    (ended_base s).global.nextPointerTag = (two_base s).global.nextPointerTag ∧
    (ended_base s).retagMode = s.tracker.retagMode := ⟨rfl,rfl⟩

/-- All old tags distinct from the len protector keep their actual initial
protection lookup through insertion and the real singleton endCall. -/
theorem contains_base (s : GenericSharedRejectedInput.Base) (query : BorTag)
    (different : query ≠ (one_base s).global.nextPointerTag) :
    (ended_base s).global.protectedTags.contains query = s.tracker.global.protectedTags.contains query :=
  ProtectorRoundTrip.singleton_contains (two_base s).global s.id (one_base s).global.nextPointerTag query .StrongProtector different

theorem ended_fields (s : GenericSharedRejectedInput.Input) :
    (ended s).global.nextPointerTag = (two s).global.nextPointerTag ∧
    (ended s).retagMode = s.tracker.retagMode := ended_fields_base s

theorem contains (s : GenericSharedRejectedInput.Input) (query : BorTag)
    (different : query ≠ (one s).global.nextPointerTag) :
    (ended s).global.protectedTags.contains query = s.tracker.global.protectedTags.contains query :=
  contains_base s query different

end
end DuplicatePrefix.GenericSharedRejectedStages
