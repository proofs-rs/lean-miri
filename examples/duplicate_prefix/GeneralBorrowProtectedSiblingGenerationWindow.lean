import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationBounds
import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationStep
import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationWindowSeed
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationWindow
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProtectedSiblingGenerationWindowSeed GeneralRangeMapState GeneralBorrowExposureCardinality
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

structure Snapshot where
  tree : BorrowTree
  global : GlobalState
  frame : FrameState
  tags : List BorTag

def loop (capacity : UInt64) : List Bool → Snapshot → Except GlobalStateError Snapshot
  | [],state => pure state
  | selected::rest,state => do
    let output ← GeneralBorrowForestFnEntry.operation state.tree state.global state.frame allocation BorTag.one 0 capacity .VisitChildrenOfAccessed
    let mutation := GeneralBorrowProtectedSiblingGenerationStep.expose output.child.tree output.global.protectedTags output.tag selected
    loop capacity rest ⟨mutation.tree,output.global,output.frame,state.tags++[output.tag]⟩

/-- A finite positive-capacity full-window source constructor/exposure schedule. Each boolean selects
actual exposure of that newly constructed sibling, including the final sibling. -/
def operation (capacity : UInt64) (selected : List Bool) : Except GlobalStateError Snapshot := do
  let (global,rootTag) ← GlobalState.new.rootPointerTag allocation
  loop capacity selected ⟨BorrowTree.new rootTag (Size.ofBytes capacity),global,{},[]⟩

structure Ready (capacity : UInt64) (selected : List Bool) where
  state : Snapshot
  actual : operation capacity selected = .ok state
  input : GeneralBorrowFreshMetadataChildMutable.Input
  tree : input.tree = state.tree
  parent : input.parent = GeneralBorrowFullSharedSeed.root
  parentTag : input.parentTag = BorTag.one
  offset : input.offset = 0
  len : input.len = capacity
  roots : input.tree.roots = #[input.parent]
  capacity : input.tree.locations.size = Size.ofBytes capacity
  allocator : GeneralBorrowGcAllocator.Invariant input.tree
  readable : Every (GeneralBorrowProtectedReadRelease.Profile input.tree state.global.protectedTags) input.tree.locations
  physical : Every (fun location => GeneralBorrowLocationSifaConsistency.Profile input.tree location state.global.protectedTags) input.tree.locations
  coherent : Every (fun location => LocationCoherent input.tree location state.global.protectedTags) input.tree.locations
  held : ∀ tag ∈ state.tags,state.global.protectedTags.contains tag = true
  distinct : state.tags.Nodup
  frame : state.frame.protectedTags = (state.tags.map (fun tag => (allocation,tag))).toArray
  count : state.tags.length = selected.length
  mapBelow : GeneralBorrowProtectedSiblingGenerationBounds.KeysBelow input.tree.tagMapping state.global.nextPointerTag.value.toNat
  protectedBelow : GeneralBorrowProtectedSiblingGenerationBounds.ProtectedBelow state.global.protectedTags state.global.nextPointerTag.value.toNat
  tagBelow : ∀ tag ∈ state.tags,tag.value.toNat < state.global.nextPointerTag.value.toNat
  mapped : ∀ tag ∈ state.tags,∃ index node,input.tree.nodeAt index = some node ∧ node.tag = tag ∧ input.tree.indexOfTag tag = some index
  earlier : ∀ tag ∈ state.tags.dropLast,∃ index,input.tree.indexOfTag tag = some index ∧
    Every (GeneralBorrowConstructorPriorPermission.At index (some (.ReservedFrz true))) input.tree.locations
end DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationWindow
