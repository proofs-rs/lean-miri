import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationStep
import duplicate_prefix.GeneralBorrowProtectedLifetimeSeed
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingGeneration
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProtectedLifetimeSeed GeneralRangeMapState GeneralBorrowExposureCardinality
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

structure Snapshot where
  tree : BorrowTree
  global : GlobalState
  frame : FrameState
  tags : List BorTag

def loop : List Bool → Snapshot → Except GlobalStateError Snapshot
  | [],state => pure state
  | selected::rest,state => do
    let output ← GeneralBorrowForestFnEntry.operation state.tree state.global state.frame allocation BorTag.one 0 1 .VisitChildrenOfAccessed
    let mutation := GeneralBorrowProtectedSiblingGenerationStep.expose output.child.tree output.global.protectedTags output.tag selected
    loop rest ⟨mutation.tree,output.global,output.frame,state.tags++[output.tag]⟩

/-- A finite one-byte source constructor/exposure schedule. Each boolean selects
actual exposure of that newly constructed sibling, including the final sibling. -/
def operation (selected : List Bool) : Except GlobalStateError Snapshot := do
  let (global,rootTag) ← GlobalState.new.rootPointerTag allocation
  loop selected ⟨BorrowTree.new rootTag (Size.ofBytes 1),global,{},[]⟩

structure Ready (selected : List Bool) where
  state : Snapshot
  actual : operation selected = .ok state
  input : GeneralBorrowFreshMetadataChildMutable.Input
  tree : input.tree = state.tree
  parent : input.parent = GeneralBorrowFullSharedSeed.root
  parentTag : input.parentTag = BorTag.one
  offset : input.offset = 0
  len : input.len = 1
  roots : input.tree.roots = #[input.parent]
  capacity : input.tree.locations.size = Size.ofBytes 1
  allocator : GeneralBorrowGcAllocator.Invariant input.tree
  readable : Every (GeneralBorrowProtectedReadRelease.Profile input.tree state.global.protectedTags) input.tree.locations
  physical : Every (fun location => GeneralBorrowLocationSifaConsistency.Profile input.tree location state.global.protectedTags) input.tree.locations
  coherent : Every (fun location => LocationCoherent input.tree location state.global.protectedTags) input.tree.locations
  held : ∀ tag ∈ state.tags,state.global.protectedTags.contains tag = true
  distinct : state.tags.Nodup
  frame : state.frame.protectedTags = (state.tags.map (fun tag => (allocation,tag))).toArray
  count : state.tags.length = selected.length
  earlier : ∀ tag ∈ state.tags.dropLast,∃ index,input.tree.indexOfTag tag = some index ∧
    Every (GeneralBorrowConstructorPriorPermission.At index (some (.ReservedFrz true))) input.tree.locations
end DuplicatePrefix.GeneralBorrowProtectedSiblingGeneration
