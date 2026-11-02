import duplicate_prefix.GeneralBorrowSparseExposedLeafDefaults
import duplicate_prefix.GeneralBorrowExposedUniqueRootFamilySeed
namespace DuplicatePrefix.GeneralBorrowSparseExposedLeafSeed
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowSparseExposedLeafState GeneralBorrowSparseExposedLeafHistory GeneralBorrowRootExposureSeed
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- A checked source family supplies sparse effective-state readiness without
reassuming any cache/profile/ownership/allocator result at the next operation. -/
def of_family (capacity : UInt64) (global : GlobalState) (tree : BorrowTree) (location : LocationTree)
    (head : UniIndex) (tail : List UniIndex)
    (family : GeneralBorrowExposedUniqueRootFamilySeed.Family capacity global tree location (head::tail))
    (short : tree.nodes.size<65536) : State capacity global.protectedTags head tail := by
  have nodes : ∀index node,tree.nodeAt index=some node→node.parent=none ∧ node.children=#[] ∧ node.isExposed=true := by
    intro index node present
    obtain ⟨actual,found,parent,leaf,exposed,stored,cache⟩:=family.leaves index (family.allNodes index node present)
    have same:=Option.some.inj (found.symm.trans present)
    subst node
    exact ⟨parent,leaf,exposed⟩
  have raw : Raw tree location global.protectedTags := by
    refine ⟨family.coherent,?_⟩
    intro index node present
    obtain ⟨actual,found,parent,leaf,exposed,stored,cache⟩:=family.leaves index (family.allNodes index node present)
    exact GeneralBorrowSparseExposedLeafDefaults.stored_unique location index node _ stored
  refine ⟨tree,Geometry.of_graph tree head tail family.structural.toGraphState family.rootsEq short nodes,
    family.structural.well,?_,?_⟩
  · rw [family.locations]
    rfl
  · rw [family.locations]
    intro position valid positive beforeUpper afterLower
    have zero : position=0 := by change position<1 at valid;omega
    subst position
    exact raw

def seeded (capacity : UInt64) (nonzero : capacity≠0) :
    State capacity GeneralBorrowProtectedLifetimeSeed.global.protectedTags root [] := by
  have family:=(GeneralBorrowExposedUniqueRootFamilySeed.seed capacity nonzero).2.2
  rw [GeneralBorrowRootExposureSeed.expose capacity nonzero BorTag.one GeneralBorrowProtectedLifetimeSeed.global.protectedTags] at family
  exact of_family capacity GeneralBorrowProtectedLifetimeSeed.global (exposedTree capacity BorTag.one) exposedLocation root [] family
    (by rw [family.size];change (1:Nat)<65536;decide)

/-- Actual root-tag allocation, BorrowTree.new and exposure feed every finite
bounded ranged wildcard Read/Write history. The reusable sparse/mixed-row
invariant and every completion are outputs of the source protocol. -/
theorem from_seed (capacity : UInt64) (nonzero : capacity≠0) (events : List (Event capacity)) :
    GlobalState.new.rootPointerTag GeneralBorrowProtectedLifetimeSeed.allocation=
      .ok (GeneralBorrowProtectedLifetimeSeed.global,BorTag.one) ∧
    (BorrowTree.new BorTag.one (Size.ofBytes capacity)).exposeTag GeneralBorrowProtectedLifetimeSeed.global.protectedTags BorTag.one=
      ⟨(seeded capacity nonzero).tree,.ok ()⟩ ∧
    Trace (seeded capacity nonzero) events (run (seeded capacity nonzero) events) := by
  refine ⟨(GeneralBorrowExposedUniqueRootFamilySeed.seed capacity nonzero).1,?_,run_trace _ events⟩
  exact GeneralBorrowRootExposureSeed.expose capacity nonzero BorTag.one GeneralBorrowProtectedLifetimeSeed.global.protectedTags
end
end DuplicatePrefix.GeneralBorrowSparseExposedLeafSeed
