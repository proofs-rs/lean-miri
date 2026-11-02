import duplicate_prefix.GeneralBorrowSparseExposedRootFormation
import duplicate_prefix.GeneralBorrowSparseExposedLeafSeed
namespace DuplicatePrefix.GeneralBorrowSparseExposedRootHistory
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowSparseExposedRootFormation GeneralBorrowSparseExposedLeafState GeneralRangeMapState GeneralBorrowRootExposureSeed
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

def seeded (capacity : UInt64) (nonzero : capacity≠0) : State capacity := by
  have family:=(GeneralBorrowExposedUniqueRootFamilySeed.seed capacity nonzero).2.2
  have initialEq:=GeneralBorrowFullSharedSeed.tree_eq capacity nonzero BorTag.one
  let initial:=BorrowTree.new BorTag.one (Size.ofBytes capacity)
  let node:=rootNode BorTag.one false
  have present : initial.nodeAt root=some node:=by change (GeneralBorrowFullSharedSeed.tree capacity nonzero BorTag.one).nodeAt root=some node;rw [initialEq];rfl
  have tagged : initial.indexOfTag BorTag.one=some root:=by change (GeneralBorrowFullSharedSeed.tree capacity nonzero BorTag.one).indexOfTag BorTag.one=some root;rw [initialEq];simp [BorrowTree.indexOfTag,UniKeyMap.get]
  have clean:=GeneralBorrowSparseExposedLeafExpose.clean initial GeneralBorrowProtectedLifetimeSeed.global.protectedTags root node present tagged
    (GeneralBorrowFullSharedSeed.depth capacity nonzero BorTag.one) (GeneralBorrowGcVacantClean.initial BorTag.one (Size.ofBytes capacity))
  have exposedEq:=GeneralBorrowRootExposureSeed.expose capacity nonzero BorTag.one GeneralBorrowProtectedLifetimeSeed.global.protectedTags
  change GeneralBorrowGcVacantClean.VacantClean ((BorrowTree.new BorTag.one (Size.ofBytes capacity)).exposeTag GeneralBorrowProtectedLifetimeSeed.global.protectedTags BorTag.one).tree at clean
  rw [exposedEq] at family clean
  let tree:=exposedTree capacity BorTag.one
  have raw : Every (fun location=>Raw tree location GeneralBorrowProtectedLifetimeSeed.global.protectedTags) tree.locations := by
    intro position valid
    have zero : position=0:=by change position<1 at valid;omega
    subst position
    refine ⟨family.coherent,?_⟩
    intro index value found
    obtain ⟨actual,known,parent,leaf,exposed,stored,cache⟩:=family.leaves index (family.allNodes index value found)
    exact GeneralBorrowSparseExposedLeafDefaults.stored_unique exposedLocation index value _ stored
  exact {
    global:=GeneralBorrowProtectedLifetimeSeed.global,tree:=tree,primary:=root,extras:=[]
    geometry:=(GeneralBorrowSparseExposedLeafSeed.seeded capacity nonzero).geometry
    structural:=family.structural,raw:=raw,clean:=clean,noFree:=family.noFree,aligned:=family.aligned,capacityEq:=rfl
    below:=by
      intro row member
      exact UInt64.lt_iff_toNat_lt.mp (family.highWater row (Array.mem_toList_iff.mpr member)) }

inductive Trace {capacity} : State capacity→List (Window capacity)→State capacity→Prop where
  | nil (s) : Trace s [] s
  | cons {s window rest final} (one : Output s window) (tail : Trace one.state rest final) : Trace s (window::rest) final

structure Generated {capacity} (s : State capacity) (windows : List (Window capacity)) where
  state : State capacity
  actual : Trace s windows state
  growth : state.tree.nodes.size=s.tree.nodes.size+windows.length
  counter : state.global.nextPointerTag.value.toNat=s.global.nextPointerTag.value.toNat+windows.length

def generate {capacity} (s : State capacity) (windows : List (Window capacity))
    (room : s.tree.nodes.size+windows.length<65536)
    (counterRoom : s.global.nextPointerTag.value.toNat+windows.length<65536) : Generated s windows := by
  induction windows generalizing s with
  | nil=>exact ⟨s,.nil s,by simp,by simp⟩
  | cons window rest ih=>
    let one:=build s window (by simp only [List.length_cons] at room;omega)
      (by simp only [List.length_cons] at counterRoom;omega)
    let tail:=ih one.state (by rw [one.growth];simp only [List.length_cons] at room;omega)
      (by rw [one.counter];simp only [List.length_cons] at counterRoom;omega)
    exact ⟨tail.state,.cons one tail.actual,
      by rw [tail.growth,one.growth];simp only [List.length_cons];omega,
      by rw [tail.counter,one.counter];simp only [List.length_cons];omega⟩

/-- Actual allocation/exposure then any numerically-resourced finite sequence
of partial Default wildcard-root construction and exposure forms the full
sparse effective mutable invariant internally. Constructor tags are issued by
real GlobalState.newPointerTag; locations may split and omit new permissions
outside each window. This is a constructor/exposure source protocol, not a
whole MIR reference-creation or arbitrary Rust caller-history theorem. -/
theorem from_seed (capacity : UInt64) (nonzero : capacity≠0) (windows : List (Window capacity))
    (room : windows.length+2<65536) :
    GlobalState.new.rootPointerTag GeneralBorrowProtectedLifetimeSeed.allocation=
      .ok (GeneralBorrowProtectedLifetimeSeed.global,BorTag.one) ∧
    (BorrowTree.new BorTag.one (Size.ofBytes capacity)).exposeTag GeneralBorrowProtectedLifetimeSeed.global.protectedTags BorTag.one=
      ⟨(seeded capacity nonzero).tree,.ok ()⟩ ∧
    Trace (seeded capacity nonzero) windows
      (generate (seeded capacity nonzero) windows (by change 1+windows.length<65536;omega)
        (by change 2+windows.length<65536;omega)).state := by
  exact ⟨GeneralBorrowProtectedLifetimeSeed.root_allocation,
    GeneralBorrowRootExposureSeed.expose capacity nonzero BorTag.one GeneralBorrowProtectedLifetimeSeed.global.protectedTags,
    (generate (seeded capacity nonzero) windows (by change 1+windows.length<65536;omega)
      (by change 2+windows.length<65536;omega)).actual⟩

/-- The formed mixed/sparse source state feeds the separately checked actual
bounded NONE Read/Write history API with no final permission/profile premise. -/
def State.toAccess {capacity} (s : State capacity) :
    GeneralBorrowSparseExposedLeafHistory.State capacity s.global.protectedTags s.primary s.extras :=
  ⟨s.tree,s.geometry,s.structural.well,s.capacityEq,fun position valid _ _ _=>s.raw position valid⟩
end
end DuplicatePrefix.GeneralBorrowSparseExposedRootHistory
