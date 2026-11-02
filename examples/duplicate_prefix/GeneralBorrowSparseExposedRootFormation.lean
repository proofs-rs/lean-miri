import duplicate_prefix.GeneralBorrowSparseExposedLeafConstructor
import duplicate_prefix.GeneralBorrowStructuralHistoryFrames
import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationBounds
import duplicate_prefix.TypedRetagEmpty
namespace DuplicatePrefix.GeneralBorrowSparseExposedRootFormation
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowSparseExposedLeafState GeneralRangeMapState GeneralBorrowSparseExposedLeafConstructor
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

structure State (capacity : UInt64) where
  global : GlobalState
  tree : BorrowTree
  primary : UniIndex
  extras : List UniIndex
  geometry : Geometry tree primary extras
  structural : GeneralBorrowStructuralHistoryState.State tree
  raw : Every (fun location=>Raw tree location global.protectedTags) tree.locations
  clean : GeneralBorrowGcVacantClean.VacantClean tree
  noFree : tree.tagMapping.deassigned.back?=none
  aligned : tree.tagMapping.mapping.size=tree.nodes.data.size
  capacityEq : tree.locations.size=Size.ofBytes capacity
  below : GeneralBorrowProtectedSiblingGenerationBounds.KeysBelow tree.tagMapping global.nextPointerTag.value.toNat

structure Window (capacity : UInt64) where
  offset : UInt64
  len : UInt64
  positive : len≠0
  bounds : offset.toNat+len.toNat≤capacity.toNat

def constructed {capacity} (s : State capacity) (window : Window capacity) :=
  s.tree.newChild (Size.ofBytes window.offset) .wildcard s.global.nextPointerTag
    (DedupRangeMap.new (Size.ofBytes window.len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false

def exposed {capacity} (s : State capacity) (window : Window capacity) :=
  (constructed s window).tree.exposeTag s.global.protectedTags s.global.nextPointerTag

structure Output {capacity} (s : State capacity) (window : Window capacity) where
  state : State capacity
  allocated : s.global.newPointerTag=.ok (state.global,s.global.nextPointerTag)
  constructedDone : (constructed s window).outcome=.ok ()
  exposedDone : (exposed s window).outcome=.ok ()
  actual : state.tree=(exposed s window).tree
  growth : state.tree.nodes.size=s.tree.nodes.size+1
  counter : state.global.nextPointerTag.value.toNat=s.global.nextPointerTag.value.toNat+1

/-- Real counter allocation, partial Default wildcard-root construction and
exposure form sparse mixed permissions. Outside the requested window, the new
leaf has its actual lazy reservation; inside, its reservation is materialized.
Every old/new scalar, coherent counter and allocator/clean resource is derived.
This library constructor/exposure protocol does not assert a full MIR FnEntry. -/
def build {capacity} (s : State capacity) (window : Window capacity)
    (room : s.tree.nodes.size+1<65536) (counterRoom : s.global.nextPointerTag.value.toNat+1<65536) : Output s window := by
  let tag:=s.global.nextPointerTag
  have freshTag:=GeneralBorrowProtectedSiblingGenerationBounds.map_fresh _ _ s.below tag (Nat.le_refl _)
  have freshGlobal : tag.value<18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change tag.value.toNat<18446744073709551615
    change tag.value.toNat+1<65536 at counterRoom
    omega
  let advanced : GlobalState:={s.global with nextPointerTag:=TypedRetagEmpty.successorTag tag freshGlobal}
  have successor : advanced.nextPointerTag.value.toNat=tag.value.toNat+1:=GeneralBorrowProtectedSiblingGenerationBounds.successor_nat tag freshGlobal
  have bounds : window.offset.toNat+window.len.toNat≤s.tree.locations.size.bytes.toNat := by rw [s.capacityEq];exact window.bounds
  have ctor:=GeneralBorrowSparseExposedLeafConstructor.append s.tree s.global.protectedTags s.structural s.raw s.clean
    tag freshTag s.noFree s.aligned room window.offset window.len window.positive bounds
  let before:=after s.tree tag window.offset window.len
  let slot:=index s.tree
  let node:=WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .Read
  have present : before.nodeAt slot=some node:=
    (GeneralBorrowPositiveWildcardConstructor.geometry s.tree (mapping s.tree tag) slot tag (.ReservedFrz false) .Read
      GeneralBorrowFreshDefaultChild.inside window.offset window.len).2
  have tagged : before.indexOfTag tag=some slot:=ctor.2.1.allocator.nodeTags slot node present
  let depth:=Classical.choice ctor.2.1.depth
  have expose:=GeneralBorrowSparseExposedLeafExpose.expose before s.global.protectedTags slot node present tagged depth ctor.2.2.1
  have finalStructural:=GeneralBorrowStructuralHistoryFrames.expose before ctor.2.1 tag s.global.protectedTags
  have finalClean:=GeneralBorrowSparseExposedLeafExpose.clean before s.global.protectedTags slot node present tagged depth ctor.2.2.2.1
  have shape:=(GeneralBorrowRootExposureFrame.expose before tag slot node tagged present depth rfl s.global.protectedTags).2
  let final:=(before.exposeTag s.global.protectedTags tag).tree
  have size : final.nodes.size=s.tree.nodes.size+1:=
    (GeneralBorrowFreshMetadata.node_size before final shape.1).trans ctor.2.2.2.2.1
  have roots : final.roots=(s.primary::(s.extras++[slot])).toArray := by
    rw [GeneralBorrowFreshMetadata.roots before final shape.1]
    change s.tree.roots.push slot=_
    rw [s.geometry.roots]
    apply Array.toList_inj.mp
    simp [List.cons_append,List.append_assoc]
  have allNodes : ∀query value,final.nodeAt query=some value→value.parent=none ∧ value.children=#[] ∧ value.isExposed=true := by
    intro query value found
    change final.nodes.get query=some value at found
    rw [shape.2] at found
    by_cases same : query=slot
    · subst query
      rw [GeneralBorrowFreshLocation.get_same] at found
      cases found
      exact ⟨rfl,rfl,rfl⟩
    · rw [GeneralBorrowFreshLocation.get_other _ slot query _ same] at found
      change (s.tree.nodes.insert slot node).get query=some value at found
      rw [GeneralBorrowFreshLocation.get_other _ slot query node same] at found
      exact s.geometry.nodes query value found
  have geometry:=Geometry.of_graph final s.primary (s.extras++[slot]) finalStructural.1.toGraphState roots (by rw [size];exact room) allNodes
  have finalMap : final.tagMapping=mapping s.tree tag := by
    rw [GeneralBorrowExposureMapFrame.expose]
    rfl
  have noFree : final.tagMapping.deassigned.back?=none := by rw [finalMap];exact s.noFree
  have aligned : final.tagMapping.mapping.size=final.nodes.data.size := by
    rw [finalMap]
    simp only [mapping,Array.size_push]
    change s.tree.tagMapping.mapping.size+1=final.nodes.size
    rw [size,s.aligned]
    rfl
  have finalBelow : GeneralBorrowProtectedSiblingGenerationBounds.KeysBelow final.tagMapping advanced.nextPointerTag.value.toNat := by
    rw [finalMap]
    exact GeneralBorrowProtectedSiblingGenerationBounds.map_push s.tree.tagMapping tag.value.toNat advanced.nextPointerTag.value.toNat s.below
      tag slot s.tree.tagMapping.deassigned (by rw [successor];omega) (by rw [successor];omega)
  have capacityEq : final.locations.size=Size.ofBytes capacity:=finalStructural.2.trans (ctor.2.2.2.2.2.trans s.capacityEq)
  have actual : (constructed s window).tree=before:=congrArg BorrowTree.ChildInsertResult.tree ctor.1
  refine {
    state:=⟨advanced,final,s.primary,s.extras++[slot],geometry,finalStructural.1,expose.2,finalClean,noFree,aligned,capacityEq,finalBelow⟩
    allocated:=TypedRetagEmpty.allocate_tag s.global freshGlobal
    constructedDone:=by change (constructed s window).outcome=.ok ();rw [show constructed s window=⟨before,.ok ()⟩ from ctor.1]
    exposedDone:=by change ((constructed s window).tree.exposeTag _ _).outcome=.ok ();rw [actual];exact expose.1
    actual:=by change final=((constructed s window).tree.exposeTag _ _).tree;rw [actual]
    growth:=size,counter:=successor }
end
end DuplicatePrefix.GeneralBorrowSparseExposedRootFormation
