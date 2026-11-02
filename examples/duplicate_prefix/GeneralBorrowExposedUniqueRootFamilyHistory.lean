import duplicate_prefix.GeneralBorrowExposedUniqueRootFamilyCycle
namespace DuplicatePrefix.GeneralBorrowExposedUniqueRootFamilyHistory
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedUniqueRootFamilySeed GeneralBorrowExposedUniqueRootFamilyAppend GeneralBorrowExposedUniqueRootFamilyCycle
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

/-- Primitive source operations at one transition, including their actual outcomes. -/
def Events (capacity : UInt64) (allocation : AllocId) (global : GlobalState) (tree : BorrowTree)
    (location : LocationTree) (fresh : global.nextPointerTag.value<18446744073709551615) : Prop :=
  let held:=registered global fresh allocation
  let read:=tree.performBorrowAccessRange .wildcard Size.ZERO (Size.ofBytes capacity) .Read held.1.protectedTags .VisitChildrenOfAccessed
  let built:=read.tree.newChild Size.ZERO .wildcard global.nextPointerTag
    (DedupRangeMap.new (Size.ofBytes capacity) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
  let written:=GeneralBorrowExposedUniqueRootFamilyRelease.written capacity global tree allocation fresh
  let released:=written.tree.releaseProtector global.nextPointerTag held.1.protectedTags
  global.newPointerTag=.ok (allocated global fresh,global.nextPointerTag) ∧
    read.status=.Completed ∧ built=⟨after tree global capacity,.ok ()⟩ ∧
    written.status=.Completed ∧ released.status=.Released ∧
    released.tree=releaseTree capacity global tree location allocation fresh ∧
    released.tree.exposeTag (ended global fresh allocation).protectedTags global.nextPointerTag=
      ⟨GeneralBorrowExposedUniqueRootFamilyCycle.finalTree capacity global tree location allocation fresh,.ok ()⟩

/-- A source-ordered history whose transitions use the actual allocator,
registered protector table, wildcard constructor, Write, release and exposure. -/
inductive History (capacity : UInt64) (allocation : AllocId) :
    Nat → GlobalState → BorrowTree → LocationTree → List UniIndex →
      GlobalState → BorrowTree → LocationTree → List UniIndex → Prop where
  | zero (global tree location roots) : History capacity allocation 0 global tree location roots global tree location roots
  | step {n global tree location roots finalGlobal finalTree finalLocation finalRoots}
      (fresh : global.nextPointerTag.value<18446744073709551615)
      (room : tree.nodes.size+1<65536)
      (events : Events capacity allocation global tree location fresh)
      (tail : History capacity allocation n
        (ended global fresh allocation)
        (GeneralBorrowExposedUniqueRootFamilyCycle.finalTree capacity global tree location allocation fresh)
        (GeneralBorrowExposedUniqueRootFamilyCycle.finalLocation capacity global tree location allocation fresh)
        (roots++[index tree]) finalGlobal finalTree finalLocation finalRoots) :
      History capacity allocation (n+1) global tree location roots finalGlobal finalTree finalLocation finalRoots

/-- Numeric tag and node room suffice for any finite number of real cycles.
Every intermediate family is derived; no Unique/cache/success premise is added. -/
theorem extend (n : Nat) (capacity : UInt64) (allocation : AllocId)
    (global : GlobalState) (tree : BorrowTree) (location : LocationTree) (roots : List UniIndex)
    (family : Family capacity global tree location roots)
    (nodeRoom : tree.nodes.size+n<65536)
    (tagRoom : global.nextPointerTag.value.toNat+n≤18446744073709551615) :
    ∃ finalGlobal finalTree finalLocation finalRoots,
      History capacity allocation n global tree location roots finalGlobal finalTree finalLocation finalRoots ∧
      Family capacity finalGlobal finalTree finalLocation finalRoots ∧
      finalTree.nodes.size=tree.nodes.size+n ∧
      finalGlobal.nextPointerTag.value.toNat=global.nextPointerTag.value.toNat+n ∧
      finalGlobal.rootPointerTags=global.rootPointerTags := by
  induction n generalizing global tree location roots with
  | zero => exact ⟨global,tree,location,roots,.zero _ _ _ _,family,by omega,by omega,rfl⟩
  | succ n ih =>
    have fresh : global.nextPointerTag.value<18446744073709551615 := by
      apply UInt64.lt_iff_toNat_lt.mpr
      change global.nextPointerTag.value.toNat<18446744073709551615
      omega
    have room : tree.nodes.size+1<65536 := by omega
    have closure := cycle capacity global tree location roots family allocation fresh room
    have nextFamily := closure.2.2.2.2.2
    have constructor := GeneralBorrowExposedUniqueRootFamilyAppend.append capacity global tree location roots family allocation fresh room
    have events : Events capacity allocation global tree location fresh :=
      ⟨closure.1,constructor.2.1,constructor.2.2.1,closure.2.1,closure.2.2.1,closure.2.2.2.1,closure.2.2.2.2.1⟩
    have nextSize : (GeneralBorrowExposedUniqueRootFamilyCycle.finalTree capacity global tree location allocation fresh).nodes.size=tree.nodes.size+1 := by
      rw [nextFamily.size,List.length_append,List.length_singleton,←family.size]
    have nextTag : (ended global fresh allocation).nextPointerTag.value.toNat=global.nextPointerTag.value.toNat+1 :=
      GenericFunctionEntryNumerics.successor_value global.nextPointerTag fresh
    obtain ⟨finalGlobal,finalTree,finalLocation,finalRoots,history,valid,size,counter,rootCache⟩ :=
      ih (ended global fresh allocation)
        (GeneralBorrowExposedUniqueRootFamilyCycle.finalTree capacity global tree location allocation fresh)
        (GeneralBorrowExposedUniqueRootFamilyCycle.finalLocation capacity global tree location allocation fresh)
        (roots++[index tree]) nextFamily (by rw [nextSize];omega) (by rw [nextTag];omega)
    exact ⟨finalGlobal,finalTree,finalLocation,finalRoots,.step fresh room events history,valid,by omega,by omega,rootCache⟩
/-- The real initial root allocation/exposure followed by any numerically
admissible number of cycles generates all exposed Unique root rows. This is
formation inside SourceModel, with no claim about Rust execution reachability. -/
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
      Family capacity finalGlobal finalTree finalLocation finalRoots ∧
      finalTree.nodes.size=1+n ∧ finalGlobal.nextPointerTag.value.toNat=2+n ∧
      finalGlobal.rootPointerTags=GeneralBorrowProtectedLifetimeSeed.global.rootPointerTags := by
  have seeded := seed capacity nonzero
  have exposed := GeneralBorrowRootExposureSeed.expose capacity nonzero BorTag.one
    GeneralBorrowProtectedLifetimeSeed.global.protectedTags
  have initial := seeded.2
  dsimp only at initial
  rw [exposed] at initial
  refine ⟨seeded.1,exposed,?_⟩
  exact extend n capacity GeneralBorrowProtectedLifetimeSeed.allocation
    GeneralBorrowProtectedLifetimeSeed.global
    (GeneralBorrowRootExposureSeed.exposedTree capacity BorTag.one)
    GeneralBorrowRootExposureSeed.exposedLocation [GeneralBorrowRootExposureSeed.root]
    initial.2 nodeRoom tagRoom
end DuplicatePrefix.GeneralBorrowExposedUniqueRootFamilyHistory
