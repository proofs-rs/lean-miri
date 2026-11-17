import duplicate_prefix.CurrentCallEmptyMaterializedWildcard
import duplicate_prefix.CurrentCallEmptyEntrySourceData
import duplicate_prefix.S04ZeroConcreteRuntime
import duplicate_prefix.S04ZeroWildcardRuntime
import duplicate_prefix.S03MaterializableRootRuntime
namespace DuplicatePrefix.CurrentCallEmptyMaterializedSourceFacts
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

private theorem fresh (root tag : BorTag) (size : Size) (distinct : root≠tag) :
    GeneralBorrowTagMap.Fresh (BorrowTree.new root size).tagMapping tag := by
  intro row member
  change row∈(#[(root,(⟨0⟩ : UniIndex))] : Array (BorTag×UniIndex)) at member
  have equal : row=(root,(⟨0⟩ : UniIndex)) := by simpa only [Array.mem_singleton] using member
  rw [equal]
  exact distinct

theorem concrete_leaf (root tag : BorTag) (size : Size) (distinct : root≠tag) :
    CurrentCallEmptyEntrySourceData.Leaf (TypedRetagConcreteEmpty.lazyTree root tag size.bytes) tag := by
  refine ⟨⟨1⟩,_,BorrowRangeAccess.canonical_child_index root tag _ distinct,by rfl,rfl,rfl,rfl,?_⟩
  intro cursor valid
  dsimp only [TypedRetagConcreteEmpty.lazyTree,BorrowRangeAccess.canonicalChildTree] at valid ⊢
  unfold DedupRangeMap.new at valid ⊢
  by_cases zero : size.bytes==0
  · simp only [Size.ofBytes,zero,↓reduceIte,Array.size_empty,Nat.not_lt_zero] at valid
  · simp only [Size.ofBytes,zero,Bool.false_eq_true,↓reduceIte,Array.size_singleton] at valid ⊢
    have cursorEq : cursor=0 := by omega
    subst cursor
    rfl

theorem wildcard_leaf (root tag : BorTag) (size : Size) (distinct : root≠tag)
    (clean : GeneralBorrowGcVacantClean.VacantClean (BorrowTree.new root size)) :
    CurrentCallEmptyEntrySourceData.Leaf (CurrentCallEmptyMaterializedWildcard.finalTree root tag size) tag := by
  let slot:=CurrentCallEmptyMaterializedWildcard.rootSlot root size
  refine ⟨slot.index,WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None,
    GeneralBorrowTagMap.pushed_get_new _ tag (fresh root tag size distinct) slot.index slot.free,
    GeneralBorrowFreshLocation.get_same (BorrowTree.new root size).nodes slot.index _,rfl,rfl,rfl,?_⟩
  intro cursor valid
  have empty:=clean slot.index slot.vacant cursor valid
  change (((BorrowTree.new root size).locations.entries[cursor].data.perms.get slot.index).getD _).accessed=false
  rw [empty]
  rfl

theorem concrete_runtime (root tag : BorTag) (size : Size) (global : GlobalState)
    (rootBelow : root.value.toNat<global.nextPointerTag.value.toNat)
    (protectors : ∀row∈global.protectedTags.entries,row.1.value.toNat<global.nextPointerTag.value.toNat)
    (distinct : root≠tag) (tagBelow : tag.value.toNat<global.nextPointerTag.value.toNat)
    (held : global.protectedTags.contains tag=true) (offset : UInt64) :
    DuplicatePrefixBorrowContract.RuntimeFacts (TypedRetagConcreteEmpty.lazyTree root tag size.bytes) global := by
  have seed:=S03MaterializableRootRuntime.initial root size.bytes global rootBelow protectors
  have facts:=S04ZeroConcreteRuntime.construct (BorrowTree.new root size) global seed root ⟨0⟩
    (GeneralBorrowFullSharedSeed.node root) (BorrowRangeAccess.new_root_index root size) (by rfl)
    tag (fresh root tag size distinct) (by change 2≤4294967295;decide) tagBelow held offset
  have actual:=ChildConstructor.new_child_zero_exact root tag distinct size.bytes offset
  have sizeEq : Size.ofBytes size.bytes=size := by cases size;rfl
  rw [sizeEq] at actual
  have next:=facts.2.1
  change DuplicatePrefixBorrowContract.RuntimeFacts
    ((BorrowTree.new root size).newChild (Size.ofBytes offset) (.concrete root) tag
      (DedupRangeMap.new Size.ZERO ChildBorrow.fnEntryLocation) (.ReservedFrz false) true).tree global at next
  rw [actual] at next
  exact next

theorem wildcard_runtime (root tag : BorTag) (size : Size) (global : GlobalState)
    (rootBelow : root.value.toNat<global.nextPointerTag.value.toNat)
    (protectors : ∀row∈global.protectedTags.entries,row.1.value.toNat<global.nextPointerTag.value.toNat)
    (distinct : root≠tag) (tagBelow : tag.value.toNat<global.nextPointerTag.value.toNat)
    (held : global.protectedTags.contains tag=true) (offset : UInt64) :
    DuplicatePrefixBorrowContract.RuntimeFacts (CurrentCallEmptyMaterializedWildcard.finalTree root tag size) global := by
  have seed:=S03MaterializableRootRuntime.initial root size.bytes global rootBelow protectors
  have facts:=S04ZeroWildcardRuntime.construct (BorrowTree.new root size) global seed tag
    (fresh root tag size distinct) (by change 2≤4294967295;decide) tagBelow held offset
  have actual:=(CurrentCallEmptyMaterializedWildcard.rootSlot root size).child tag (fresh root tag size distinct) offset
  rw [actual] at facts
  exact facts.2.1
end
end DuplicatePrefix.CurrentCallEmptyMaterializedSourceFacts

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallEmptyMaterializedSourceFacts.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved materialized-empty dependency {name}: {dependency}"
