import duplicate_prefix.GeneralBorrowProtectedSiblingFunctionCaller
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingFunctionNumerics
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open GenericFunctionEntryState GeneralBorrowProtectedSiblingFunctionCaller GeneralBorrowProtectedSiblingGenerationBounds
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
noncomputable section
variable {tree : BorrowTree} {global : GlobalState} {bytes : UInt64}

def tag (s : Caller tree global bytes) : Fin 6 → BorTag
  | ⟨0,_⟩ => s.tracker.global.nextPointerTag
  | ⟨1,_⟩ => (next s.tracker s.fresh).global.nextPointerTag
  | ⟨2,_⟩ => (held s.tracker s.fresh s.slotFresh).global.nextPointerTag
  | ⟨3,_⟩ => (ReferenceBorrowDriver.allocatedTracker (held s.tracker s.fresh s.slotFresh) s.fresh3).global.nextPointerTag
  | ⟨4,_⟩ => (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held s.tracker s.fresh s.slotFresh) s.fresh3) s.fresh4).global.nextPointerTag
  | ⟨5,_⟩ => (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held s.tracker s.fresh s.slotFresh) s.fresh3) s.fresh4) s.fresh5).global.nextPointerTag

theorem tag_nat (s : Caller tree global bytes) (i : Fin 6) :
    (tag s i).value.toNat = s.tracker.global.nextPointerTag.value.toNat+i.val := by
  have h1 : (tag s 1).value.toNat = (tag s 0).value.toNat+1 := successor_nat _ s.fresh
  have h2 : (tag s 2).value.toNat = (tag s 1).value.toNat+1 := successor_nat _ s.slotFresh
  have h3 : (tag s 3).value.toNat = (tag s 2).value.toNat+1 := successor_nat _ s.fresh3
  have h4 : (tag s 4).value.toNat = (tag s 3).value.toNat+1 := successor_nat _ s.fresh4
  have h5 : (tag s 5).value.toNat = (tag s 4).value.toNat+1 := successor_nat _ s.fresh5
  have h0 : (tag s 0).value.toNat = s.tracker.global.nextPointerTag.value.toNat := rfl
  rcases i with ⟨i,bounded⟩
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  rcases cases with h|h|h|h|h|h <;> subst i <;> simp only [tag,Fin.val_mk] at * <;> omega

theorem tag_fresh (s : Caller tree global bytes)
    (below : KeysBelow tree.tagMapping global.nextPointerTag.value.toNat) (i : Fin 6) :
    GeneralBorrowTagMap.Fresh tree.tagMapping (tag s i) := by
  apply map_fresh _ _ below
  rw [tag_nat,s.globalEq]
  omega

theorem different (s : Caller tree global bytes) (i j : Fin 6) (different : i ≠ j) : tag s i ≠ tag s j := by
  intro same
  have equal := congrArg (fun tag : BorTag => tag.value.toNat) same
  rw [tag_nat,tag_nat] at equal
  apply different
  apply Fin.ext
  omega

theorem unheld (s : Caller tree global bytes) (empty : global.protectedTags = {})
    (i : Fin 6) (later : 2 ≤ i.val) :
    (held s.tracker s.fresh s.slotFresh).global.protectedTags.get (tag s i) = none := by
  have empty' : s.tracker.global.protectedTags = {} := by rw [s.globalEq,empty]
  change ((s.tracker.global.protectedTags.insert (tag s 0) .StrongProtector).insert (tag s 1) .StrongProtector).get (tag s i) = none
  rw [GeneralBorrowProtectorCacheMap.insert_other _ _ _ _ (different s i 1 (by intro equal;subst i;omega)),
      GeneralBorrowProtectorCacheMap.insert_other _ _ _ _ (different s i 0 (by intro equal;subst i;omega)),empty']
  rfl

theorem helper_table (s : Caller tree global bytes) (empty : global.protectedTags = {}) :
    ((TypedBorrowSteps.registeredTracker
      (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held s.tracker s.fresh s.slotFresh) s.fresh3) s.fresh4)
      (tag s 3)).global.endCall (({} : FrameState).addProtector s.id (tag s 3))).protectedTags =
      (held s.tracker s.fresh s.slotFresh).global.protectedTags := by
  have empty' : s.tracker.global.protectedTags = {} := by rw [s.globalEq,empty]
  have d01 := different s 0 1 (by decide)
  have d03 := different s 0 3 (by decide)
  have d13 := different s 1 3 (by decide)
  change (((s.tracker.global.protectedTags.insert (tag s 0) .StrongProtector).insert (tag s 1) .StrongProtector).insert
    (tag s 3) .StrongProtector).remove (tag s 3) =
    (s.tracker.global.protectedTags.insert (tag s 0) .StrongProtector).insert (tag s 1) .StrongProtector
  simp [empty',ProtectedTags.insert,ProtectedTags.remove,d01,d03,d13]

end
end DuplicatePrefix.GeneralBorrowProtectedSiblingFunctionNumerics
