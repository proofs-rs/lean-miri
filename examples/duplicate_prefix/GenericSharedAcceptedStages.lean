import duplicate_prefix.GenericSharedAcceptedInput
import duplicate_prefix.GeneralBorrowFreshSharedNextPool
import duplicate_prefix.ProtectorRoundTrip
namespace DuplicatePrefix.GenericSharedAcceptedStages
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
noncomputable section

def one_base (s : GenericSharedAcceptedInput.Base) := ReferenceBorrowDriver.allocatedTracker s.tracker s.fresh

def two_base (s : GenericSharedAcceptedInput.Base) := ReferenceBorrowDriver.allocatedTracker (one_base s) s.fresh2

def three_base (s : GenericSharedAcceptedInput.Base) := ReferenceBorrowDriver.allocatedTracker (two_base s) s.fresh3

def held_base (s : GenericSharedAcceptedInput.Base) := TypedBorrowSteps.registeredTracker (two_base s) (one_base s).global.nextPointerTag

def ended_base (s : GenericSharedAcceptedInput.Base) :=
  {held_base s with global := (held_base s).global.endCall (({} : FrameState).addProtector s.id (one_base s).global.nextPointerTag)}

/-- The actual second shared child for arbitrary, already-derived input data. -/
def child_data (s : GenericSharedAcceptedInput.Base)
    (second : GeneralBorrowFreshSharedSequence.Data
      (GeneralBorrowFreshSharedSequence.child s.first s.tracker.global.protectedTags false).tree
      (one_base s).global.nextPointerTag (GeneralBorrowFreshSharedSequence.index s.first) s.offset s.len) :=
  (GeneralBorrowFreshSharedSequence.child second s.tracker.global.protectedTags true).tree

/-- Allocating, registering and ending the len protector changes neither the
next-tag value nor the retag mode inherited from the initial root tracker. -/
theorem ended_fields_base (s : GenericSharedAcceptedInput.Base) :
    (ended_base s).global.nextPointerTag = (two_base s).global.nextPointerTag ∧
    (ended_base s).retagMode = s.tracker.retagMode := ⟨rfl,rfl⟩

/-- Other initial protection lookups survive the singleton len scope. -/
theorem contains_base (s : GenericSharedAcceptedInput.Base) (query : BorTag)
    (different : query ≠ (one_base s).global.nextPointerTag) :
    (ended_base s).global.protectedTags.contains query = s.tracker.global.protectedTags.contains query :=
  ProtectorRoundTrip.singleton_contains (two_base s).global s.id (one_base s).global.nextPointerTag query .StrongProtector different

theorem next_fields_base (s : GenericSharedAcceptedInput.Base)
    (fresh : (ended_base s).global.nextPointerTag.value < 18446744073709551615) :
    (ReferenceBorrowDriver.allocatedTracker (ended_base s) fresh).global.nextPointerTag = (three_base s).global.nextPointerTag := rfl

-- Preserve the original append-only APIs as projections of common stages.
def one (s : GenericSharedAcceptedInput.Input) := one_base s.toBase
def two (s : GenericSharedAcceptedInput.Input) := two_base s.toBase
def three (s : GenericSharedAcceptedInput.Input) := three_base s.toBase
def held (s : GenericSharedAcceptedInput.Input) := held_base s.toBase
def ended (s : GenericSharedAcceptedInput.Input) := ended_base s.toBase

def second (s : GenericSharedAcceptedInput.Input) :=
  (GeneralBorrowFreshSharedNext.next s.entry.allocation.extra s.tracker.global.protectedTags s.target
    s.tracker.global.nextPointerTag (one s).global.nextPointerTag s.offset s.len s.first s.noFree s.room
    s.tagFresh s.protectorFresh s.different s.cleanFuture s.owned).val

def child (s : GenericSharedAcceptedInput.Input) := child_data s.toBase (second s)

theorem ended_fields (s : GenericSharedAcceptedInput.Input) :
    (ended s).global.nextPointerTag = (two s).global.nextPointerTag ∧
    (ended s).retagMode = s.tracker.retagMode := ended_fields_base s.toBase

theorem contains (s : GenericSharedAcceptedInput.Input) (query : BorTag)
    (different : query ≠ (one s).global.nextPointerTag) :
    (ended s).global.protectedTags.contains query = s.tracker.global.protectedTags.contains query :=
  contains_base s.toBase query different

theorem next_fields (s : GenericSharedAcceptedInput.Input)
    (fresh : (ended s).global.nextPointerTag.value < 18446744073709551615) :
    (ReferenceBorrowDriver.allocatedTracker (ended s) fresh).global.nextPointerTag = (three s).global.nextPointerTag :=
  next_fields_base s.toBase fresh

/-- Choose the next shared Data from initial pool invariants, not from a
post-state or successful-operation premise. -/
def second_pool (s : GenericSharedAcceptedInput.PoolInput) :=
  (GeneralBorrowFreshSharedNextPool.next s.entry.allocation.extra s.tracker.global.protectedTags s.target
    s.tracker.global.nextPointerTag (one_base s.toBase).global.nextPointerTag s.offset s.len s.first
    s.pool s.accounting (by have bound := s.nodeRoom;omega) s.tagFresh s.protectorFresh s.different
    s.cleanVacant s.owned).val

def child_pool (s : GenericSharedAcceptedInput.PoolInput) := child_data s.toBase (second_pool s)

theorem second_pool_parent (s : GenericSharedAcceptedInput.PoolInput) :
    (second_pool s).parentTag = s.tracker.global.nextPointerTag := rfl
end
end DuplicatePrefix.GenericSharedAcceptedStages
