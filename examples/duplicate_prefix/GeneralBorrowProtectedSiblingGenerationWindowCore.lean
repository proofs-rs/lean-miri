import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationWindow
import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationBounds
import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationConflict
import duplicate_prefix.GeneralBorrowTwoProtectedStateInfoSeed
import duplicate_prefix.GeneralBorrowTwoProtectedStateInfoFullRange
import duplicate_prefix.GeneralBorrowExposureAllocation
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationWindowCore
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProtectedSiblingGenerationWindowSeed GeneralRangeMapState GeneralBorrowExposureCardinality
open GeneralBorrowProtectedSiblingGenerationBounds GeneralBorrowProtectedSiblingGenerationWindow
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

structure Descriptor (tree : BorrowTree) (root : UniIndex) (tag : BorTag) where
  index : UniIndex
  node : TreeNode
  present : tree.nodeAt index = some node
  tagged : node.tag = tag
  parent : node.parent = some root
  leaf : node.children = #[]
  defaultPermission : node.defaultInitialPermission = .ReservedFrz false

def Earlier (input : GeneralBorrowFreshMetadataChildMutable.Input) (tags : List BorTag) : Prop :=
  tags = [] ∨ ∃ past tag index,tags = past++[tag] ∧ input.tree.indexOfTag tag = some index ∧
    GeneralBorrowDefaultReservationType.TreeTyped input.tree index ∧
    ∀ earlier ∈ past,∃ query,input.tree.indexOfTag earlier = some query ∧
      Every (GeneralBorrowConstructorPriorPermission.At query (some (.ReservedFrz true))) input.tree.locations

structure Core (capacity : UInt64) (remaining : Nat) where
  input : GeneralBorrowFreshMetadataChildMutable.Input
  global : GlobalState
  frame : FrameState
  tags : List BorTag
  tag : input.newTag = global.nextPointerTag
  parentTag : input.parentTag = BorTag.one
  parent : input.parent = GeneralBorrowFullSharedSeed.root
  offset : input.offset = 0
  len : input.len = capacity
  roots : input.tree.roots = #[input.parent]
  capacity : input.tree.locations.size = Size.ofBytes capacity
  allocator : GeneralBorrowGcAllocator.Invariant input.tree
  readable : Every (GeneralBorrowProtectedReadRelease.Profile input.tree global.protectedTags) input.tree.locations
  physical : Every (fun location => GeneralBorrowLocationSifaConsistency.Profile input.tree location global.protectedTags) input.tree.locations
  coherent : Every (fun location => LocationCoherent input.tree location global.protectedTags) input.tree.locations
  mapBelow : KeysBelow input.tree.tagMapping global.nextPointerTag.value.toNat
  protectedBelow : ProtectedBelow global.protectedTags global.nextPointerTag.value.toNat
  tagBelow : ∀ old ∈ tags,old.value.toNat < global.nextPointerTag.value.toNat
  tagRoom : global.nextPointerTag.value.toNat+remaining ≤ 4294967295
  nodeRoom : input.tree.tagMapping.mapping.size+remaining+1 ≤ 4294967295
  held : ∀ old ∈ tags,global.protectedTags.contains old = true
  distinct : tags.Nodup
  frameTags : frame.protectedTags = (tags.map (fun tag => (allocation,tag))).toArray
  descriptors : ∀ old ∈ tags,Nonempty (Descriptor input.tree input.parent old)
  earlier : Earlier input tags

def snapshot {capacity remaining} (state : Core capacity remaining) : Snapshot := ⟨state.input.tree,state.global,state.frame,state.tags⟩

/-- All initial data comes from the actual root allocation and one-byte tree.
The sole resource is finite numeric headroom for the selected schedule. -/
def seed (capacity : UInt64) (nonzero : capacity ≠ 0) (remaining : Nat) (room : remaining+2 ≤ 4294967295) : Core capacity remaining := {
  input := input capacity nonzero,global := global,frame := {},tags := [],tag := rfl,parentTag := rfl,parent := rfl,offset := rfl,len := rfl,roots := rfl,capacity := by
    change (GeneralBorrowFullSharedSeed.tree capacity nonzero BorTag.one).locations.size = Size.ofBytes capacity
    rw [GeneralBorrowFullSharedSeed.tree_eq]
    rfl
  allocator := GeneralBorrowGcAllocator.initial BorTag.one (Size.ofBytes capacity)
  readable := profile capacity nonzero
  physical := GeneralBorrowAllocationSifaConsistency.allocation capacity BorTag.one {}
  coherent := GeneralBorrowExposureAllocation.coherent capacity BorTag.one {}
  mapBelow := by
    intro row member
    change row ∈ #[(BorTag.one,GeneralBorrowFullSharedSeed.root)] at member
    have same := Array.mem_singleton.mp member
    subst row
    decide
  protectedBelow := by intro row member;change row ∈ (#[] : Array (BorTag×ProtectorKind)) at member;simp at member
  tagBelow := by intro old member;simp at member
  tagRoom := by change 2+remaining ≤ 4294967295;omega
  nodeRoom := by change 1+remaining+1 ≤ 4294967295;omega
  held := by intro old member;simp at member
  distinct := .nil
  frameTags := rfl
  descriptors := by intro old member;simp at member
  earlier := .inl rfl }

structure Advance {capacity : UInt64} {remaining : Nat} (before : Core capacity (remaining+1)) (selected : Bool) where
  next : Core capacity remaining
  actual : ∀ tail, loop capacity (selected::tail) (snapshot before) = loop capacity tail (snapshot next)
  count : next.tags.length = before.tags.length+1
end DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationWindowCore
