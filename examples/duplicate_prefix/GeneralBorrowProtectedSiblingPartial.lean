import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationWindowCore
import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationWindowFalseStep
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingPartial
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapState GeneralBorrowExposureCardinality
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

/-- A raw positive byte window. Arbitrary overlap and chronological order are allowed. -/
structure Window (capacity : UInt64) where
  offset : UInt64
  len : UInt64
  nonzero : len ≠ 0
  bounded : offset.toNat+len.toNat ≤ capacity.toNat

abbrev Snapshot := GeneralBorrowProtectedSiblingGenerationWindow.Snapshot

def slice (input : GeneralBorrowFreshMetadataChildMutable.Input) {capacity : UInt64}
    (size : input.tree.locations.size = Size.ofBytes capacity) (window : Window capacity) :
    GeneralBorrowFreshMetadataChildMutable.Input :=
  {input with
    offset := window.offset,len := window.len,nonzero := window.nonzero,
    bounds := by rw [size];exact window.bounded}

def full (input : GeneralBorrowFreshMetadataChildMutable.Input) {capacity : UInt64}
    (size : input.tree.locations.size = Size.ofBytes capacity) (nonzero : capacity ≠ 0) :
    GeneralBorrowFreshMetadataChildMutable.Input :=
  {input with
    offset := 0,len := capacity,nonzero := nonzero,bounds := by rw [size];change 0+capacity.toNat ≤ capacity.toNat;omega}

def loop {capacity : UInt64} : List (Window capacity) → Snapshot → Except GlobalStateError Snapshot
  | [],state => pure state
  | window::rest,state => do
    let output ← GeneralBorrowForestFnEntry.operation state.tree state.global state.frame
      GeneralBorrowProtectedSiblingGenerationWindowSeed.allocation BorTag.one window.offset window.len .VisitChildrenOfAccessed
    loop rest ⟨output.child.tree,output.global,output.frame,state.tags++[output.tag]⟩

def operation (capacity : UInt64) (windows : List (Window capacity)) : Except GlobalStateError Snapshot := do
  let (global,rootTag) ← GlobalState.new.rootPointerTag GeneralBorrowProtectedSiblingGenerationWindowSeed.allocation
  loop windows ⟨BorrowTree.new rootTag (Size.ofBytes capacity),global,{},[]⟩

/-- Only the most recently constructed sibling is globally unconflicted.
Older conflicts are tracked on overlap ranges rather than assumed everywhere. -/
def Latest (input : GeneralBorrowFreshMetadataChildMutable.Input) {capacity : UInt64}
    (origins : List (BorTag × Window capacity)) : Prop :=
  origins = [] ∨ ∃ past tag window index,origins = past++[(tag,window)] ∧ input.tree.indexOfTag tag = some index ∧
    GeneralBorrowDefaultReservationType.TreeTyped input.tree index

structure Ready (bytes : UInt64) (windows : List (Window bytes)) where
  state : Snapshot
  actual : operation bytes windows = .ok state
  input : GeneralBorrowFreshMetadataChildMutable.Input
  tree : input.tree = state.tree
  parent : input.parent = GeneralBorrowFullSharedSeed.root
  parentTag : input.parentTag = BorTag.one
  offset : input.offset = 0
  len : input.len = bytes
  roots : input.tree.roots = #[input.parent]
  capacity : input.tree.locations.size = Size.ofBytes bytes
  allocator : GeneralBorrowGcAllocator.Invariant input.tree
  readable : Every (GeneralBorrowProtectedReadRelease.Profile input.tree state.global.protectedTags) input.tree.locations
  physical : Every (fun location => GeneralBorrowLocationSifaConsistency.Profile input.tree location state.global.protectedTags) input.tree.locations
  coherent : Every (fun location => LocationCoherent input.tree location state.global.protectedTags) input.tree.locations
  held : ∀ tag ∈ state.tags,state.global.protectedTags.contains tag = true
  distinct : state.tags.Nodup
  frame : state.frame.protectedTags = (state.tags.map (fun tag => (GeneralBorrowProtectedSiblingGenerationWindowSeed.allocation,tag))).toArray
  count : state.tags.length = windows.length
  rootUnique : Every (GeneralBorrowConstructorPriorPermission.At input.parent (some .Unique)) input.tree.locations
  hidden : GeneralBorrowFreshProtectedSlotFlags.Unexposed input.tree
  nodes : input.tree.nodes.size = windows.length+1
  origins : List (BorTag × Window bytes)
  latest : Latest input origins
  originTags : origins.map Prod.fst = state.tags
  originWindows : origins.map Prod.snd = windows
  descriptors : ∀ tag ∈ state.tags,Nonempty (GeneralBorrowProtectedSiblingGenerationWindowCore.Descriptor input.tree input.parent tag)
  mapBelow : GeneralBorrowProtectedSiblingGenerationBounds.KeysBelow input.tree.tagMapping state.global.nextPointerTag.value.toNat
  protectedBelow : GeneralBorrowProtectedSiblingGenerationBounds.ProtectedBelow state.global.protectedTags state.global.nextPointerTag.value.toNat
  tagBelow : ∀ tag ∈ state.tags,tag.value.toNat < state.global.nextPointerTag.value.toNat
end DuplicatePrefix.GeneralBorrowProtectedSiblingPartial
