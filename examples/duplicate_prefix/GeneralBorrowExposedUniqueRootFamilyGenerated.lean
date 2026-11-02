import duplicate_prefix.GeneralBorrowExposedUniqueRootFamilyHistoryClean
namespace DuplicatePrefix.GeneralBorrowExposedUniqueRootFamilyGenerated
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedUniqueRootFamilySeed GeneralBorrowExposedUniqueRootFamilyHistory
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Endpoints and derived certificates of an actual SourceModel generation.
Physical callers may refer to these endpoints without assuming any borrow row. -/
structure Generated (capacity : UInt64) (cycles : Nat) where
  global : GlobalState
  tree : BorrowTree
  location : LocationTree
  roots : List UniIndex
  allocated : GlobalState.new.rootPointerTag GeneralBorrowProtectedLifetimeSeed.allocation=
    .ok (GeneralBorrowProtectedLifetimeSeed.global,BorTag.one)
  exposed : (BorrowTree.new BorTag.one (Size.ofBytes capacity)).exposeTag
    GeneralBorrowProtectedLifetimeSeed.global.protectedTags BorTag.one=
    ⟨GeneralBorrowRootExposureSeed.exposedTree capacity BorTag.one,.ok ()⟩
  history : History capacity GeneralBorrowProtectedLifetimeSeed.allocation cycles
    GeneralBorrowProtectedLifetimeSeed.global
    (GeneralBorrowRootExposureSeed.exposedTree capacity BorTag.one)
    GeneralBorrowRootExposureSeed.exposedLocation [GeneralBorrowRootExposureSeed.root]
    global tree location roots
  family : Family capacity global tree location roots
  vacantClean : GeneralBorrowGcVacantClean.VacantClean tree
  size : tree.nodes.size=1+cycles
  counter : global.nextPointerTag.value.toNat=2+cycles
  rootCache : global.rootPointerTags=GeneralBorrowProtectedLifetimeSeed.global.rootPointerTags

theorem formed (cycles : Nat) (capacity : UInt64) (nonzero : capacity≠0)
    (nodeRoom : 1+cycles<65536) (tagRoom : 2+cycles≤18446744073709551615) :
    Nonempty (Generated capacity cycles) := by
  obtain ⟨allocated,exposed,global,tree,location,roots,history,family,clean,size,counter,cache⟩ :=
    GeneralBorrowExposedUniqueRootFamilyHistoryClean.generate cycles capacity nonzero nodeRoom tagRoom
  exact ⟨⟨global,tree,location,roots,allocated,exposed,history,family,clean,size,counter,cache⟩⟩

/-- Numeric inputs select generated endpoints; all borrow/cache/allocator
certificates are outputs of the checked real history. -/
noncomputable def build (cycles : Nat) (capacity : UInt64) (nonzero : capacity≠0)
    (nodeRoom : 1+cycles<65536) (tagRoom : 2+cycles≤18446744073709551615) :
    Generated capacity cycles := Classical.choice (formed cycles capacity nonzero nodeRoom tagRoom)
end DuplicatePrefix.GeneralBorrowExposedUniqueRootFamilyGenerated
