import duplicate_prefix.GeneralBorrowForestRawAllCountInput
namespace DuplicatePrefix.GeneralBorrowForestRawAllCountTags
open Miri Miri.Memory Miri.TreeBorrows Miri.Interpreter
open GenericFunctionEntryState GenericFunctionTagFormation GeneralBorrowForestRawAllCountInput
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

def tags (s : Initial) : Array BorTag := #[s.tracker.global.nextPointerTag,(next s.tracker s.fresh).global.nextPointerTag,
  future s.tracker (chain s) ⟨0,by decide⟩,future s.tracker (chain s) ⟨1,by decide⟩,
  future s.tracker (chain s) ⟨2,by decide⟩,future s.tracker (chain s) ⟨3,by decide⟩]

/-- Six actual GlobalState.newPointerTag effects return exactly the current,
slot, Expr, helper FnEntry, Default and final FnEntry tags used by the physical
proof. This allocation projection does not replace any retag/body operation. -/
theorem allocations (s : Initial) : ∃ allocated, allocate_six s.tracker.global=.ok (allocated,tags s) := by
  exact ⟨_,GenericFunctionTagFormation.allocate_six_ok s.tracker (chain s)⟩

theorem current_slot_different (s : Initial) : s.tracker.global.nextPointerTag≠(next s.tracker s.fresh).global.nextPointerTag := by
  apply GeneralBorrowForestTagHighWater.different
  have value := GenericFunctionEntryNumerics.successor_value s.tracker.global.nextPointerTag s.fresh
  change (next s.tracker s.fresh).global.nextPointerTag.value.toNat=s.tracker.global.nextPointerTag.value.toNat+1 at value
  omega

theorem distinct (s : Initial) : (tags s).toList.Nodup := by
  simp [tags,List.nodup_cons,root_different,future_different]
  exact ⟨current_slot_different s,slot_different s ⟨0,by decide⟩,slot_different s ⟨1,by decide⟩,
    slot_different s ⟨2,by decide⟩,slot_different s ⟨3,by decide⟩⟩

/-- Even the original current counter tag's freshness/unheld status follows
from the raw original key bounds, independently of the base-zero certificate. -/
theorem current_fresh (s : Initial) :
    GeneralBorrowTagMap.Fresh s.entry.allocation.extra.tagMapping s.tracker.global.nextPointerTag ∧
      GeneralBorrowProtector.Fresh s.entry.allocation.extra s.tracker.global.nextPointerTag ∧
      s.tracker.global.protectedTags.contains s.tracker.global.nextPointerTag=false :=
  fresh_above s.entry.allocation.extra s.tracker.global.protectedTags s.tracker.global.nextPointerTag
    s.tracker.global.nextPointerTag (below s) (Nat.le_refl _)
end
end DuplicatePrefix.GeneralBorrowForestRawAllCountTags
