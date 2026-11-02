import duplicate_prefix.GeneralBorrowExposedUniqueRootFamilyCycleClean
namespace DuplicatePrefix.GeneralBorrowExposedUniqueRootFamilyHistoryClean
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedUniqueRootFamilySeed GeneralBorrowExposedUniqueRootFamilyHistory
open GeneralBorrowGcVacantClean GeneralBorrowFreshFutureClean GeneralRangeMapState RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Initial real root exposure does not create a permission at any vacant index. -/
theorem seed (capacity : UInt64) (tag : BorTag) :
    VacantClean (GeneralBorrowRootExposureSeed.exposedTree capacity tag) := by
  intro query vacant position valid
  have notZero : query.toNat≠0 := by
    intro zero
    change (⟨#[some (GeneralBorrowRootExposureSeed.rootNode tag true)]⟩ : UniValMap TreeNode).get query=none at vacant
    simp [UniValMap.get,zero] at vacant
  have zero : position=0 := by change position<1 at valid;omega
  subst position
  change (⟨#[some GeneralBorrowRootExposureSeed.unique]⟩ : UniValMap LocationState).get query=none
  unfold UniValMap.get
  rw [Array.getElem?_eq_none (by change 1≤query.toNat;omega)]

/-- Every actual source-ordered history retains vacant permission cleanliness. -/
theorem preserves (capacity : UInt64) (allocation : AllocId) {n : Nat}
    {global finalGlobal : GlobalState} {tree finalTree : BorrowTree} {location finalLocation : LocationTree}
    {roots finalRoots : List UniIndex}
    (run : History capacity allocation n global tree location roots finalGlobal finalTree finalLocation finalRoots) :
    Family capacity global tree location roots → VacantClean tree →
      Family capacity finalGlobal finalTree finalLocation finalRoots ∧ VacantClean finalTree := by
  induction run with
  | zero => intro family clean;exact ⟨family,clean⟩
  | @step n global tree location roots finalGlobal finalTree finalLocation finalRoots fresh room events tail ih =>
    intro family clean
    have formed := GeneralBorrowExposedUniqueRootFamilyCycle.cycle capacity global tree location roots family allocation fresh room
    have nextClean := GeneralBorrowExposedUniqueRootFamilyCycleClean.cycle capacity global tree location roots family allocation fresh room clean
    exact ih formed.2.2.2.2.2 nextClean

/-- Numeric-room-only generation also supplies all vacant permission slots,
so downstream all-count inputs need no separate cleanliness premise. -/
theorem generate (n : Nat) (capacity : UInt64) (nonzero : capacity≠0)
    (nodeRoom : 1+n<65536) (tagRoom : 2+n≤18446744073709551615) :
    GlobalState.new.rootPointerTag GeneralBorrowProtectedLifetimeSeed.allocation=
      .ok (GeneralBorrowProtectedLifetimeSeed.global,BorTag.one) ∧
    (BorrowTree.new BorTag.one (Size.ofBytes capacity)).exposeTag
      GeneralBorrowProtectedLifetimeSeed.global.protectedTags BorTag.one=
      ⟨GeneralBorrowRootExposureSeed.exposedTree capacity BorTag.one,.ok ()⟩ ∧
    ∃ finalGlobal finalTree finalLocation finalRoots,
      History capacity GeneralBorrowProtectedLifetimeSeed.allocation n
        GeneralBorrowProtectedLifetimeSeed.global
        (GeneralBorrowRootExposureSeed.exposedTree capacity BorTag.one)
        GeneralBorrowRootExposureSeed.exposedLocation [GeneralBorrowRootExposureSeed.root]
        finalGlobal finalTree finalLocation finalRoots ∧
      Family capacity finalGlobal finalTree finalLocation finalRoots ∧ VacantClean finalTree ∧
      finalTree.nodes.size=1+n ∧ finalGlobal.nextPointerTag.value.toNat=2+n ∧
      finalGlobal.rootPointerTags=GeneralBorrowProtectedLifetimeSeed.global.rootPointerTags := by
  obtain ⟨allocated,exposed,finalGlobal,finalTree,finalLocation,finalRoots,run,family,size,counter,rootCache⟩ :=
    GeneralBorrowExposedUniqueRootFamilyHistory.generate n capacity nonzero nodeRoom tagRoom
  have initial := (GeneralBorrowExposedUniqueRootFamilySeed.seed capacity nonzero).2
  dsimp only at initial
  rw [exposed] at initial
  have clean := (preserves capacity GeneralBorrowProtectedLifetimeSeed.allocation run initial.2 (seed capacity BorTag.one)).2
  exact ⟨allocated,exposed,finalGlobal,finalTree,finalLocation,finalRoots,run,family,clean,size,counter,rootCache⟩
end DuplicatePrefix.GeneralBorrowExposedUniqueRootFamilyHistoryClean
