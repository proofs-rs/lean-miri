import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationWindowFalseStep
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationWindowFalseAdvance
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProtectedSiblingGenerationWindowSeed GeneralRangeMapState GeneralBorrowExposureCardinality
open GeneralBorrowProtectedSiblingGenerationBounds GeneralBorrowProtectedSiblingGenerationWindow GeneralBorrowProtectedSiblingGenerationWindowCore
open GeneralBorrowFreshProtectedSlotFlags
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem preserves {capacity remaining} (before : Core capacity (remaining+1))
    (advance : Advance before false) (initial : Unexposed before.input.tree) :
    Unexposed advance.next.input.tree ∧ advance.next.input.tree.nodes.size = before.input.tree.nodes.size+1 := by
  have pointerRoom : before.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    have room := before.tagRoom
    change before.global.nextPointerTag.value.toNat < 18446744073709551615
    omega
  let future := TypedRetagEmpty.successorTag before.global.nextPointerTag pointerRoom
  have futureNat : future.value.toNat = before.global.nextPointerTag.value.toNat+1 := successor_nat _ pointerRoom
  have futureFresh : GeneralBorrowTagMap.Fresh before.input.tree.tagMapping future := map_fresh _ _ before.mapBelow future (by omega)
  have different : before.input.newTag ≠ future := by
    intro same
    have equal := congrArg (fun tag : BorTag => tag.value.toNat) same
    rw [before.tag,futureNat] at equal
    omega
  have unheld : before.global.protectedTags.get before.input.newTag = none :=
    GeneralBorrowProtectedSiblingGenerationBounds.unheld _ _ before.protectedBelow before.input.newTag (by rw [before.tag];exact Nat.le_refl _)
  obtain ⟨step⟩ := GeneralBorrowProtectedSiblingGenerationStep.generate before.input before.global before.frame allocation false before.tag pointerRoom unheld before.roots
    before.readable before.physical before.coherent before.allocator future rfl futureFresh different (by have room := before.nodeRoom;omega)
  have nextFlags := GeneralBorrowProtectedSiblingGenerationWindowFalseStep.preserves before step initial
  have invoked := step.invoked
  rw [before.parentTag,before.offset,before.len] at invoked
  have actual : loop capacity [false] (snapshot before) =
      .ok ⟨step.mutation.tree,step.output.global,step.output.frame,before.tags++[step.output.tag]⟩ := by
    simp only [loop,snapshot,invoked,Except.bind,bind,pure,Except.pure]
    rw [←step.mutated]
  have same : snapshot advance.next = ⟨step.mutation.tree,step.output.global,step.output.frame,before.tags++[step.output.tag]⟩ :=
    Except.ok.inj ((advance.actual []).symm.trans actual)
  have treeEq : advance.next.input.tree = step.next.tree :=
    (congrArg Snapshot.tree same).trans step.nextTree.symm
  rw [treeEq]
  exact ⟨nextFlags,step.growth⟩
end DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationWindowFalseAdvance
