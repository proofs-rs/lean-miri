import duplicate_prefix.GeneralBorrowProtectedSiblingPartialTable
import duplicate_prefix.GeneralBorrowProtectedSiblingWindowResources
import duplicate_prefix.GeneralBorrowProtectedSiblingWindowRootOwned
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingPartialFunctionHistory
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProtectedSiblingPartial GeneralBorrowProtectedReleaseHistory GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

abbrev Output := GeneralBorrowProtectedSiblingWindowLifetimes.Output

def operation (bytes : UInt64) (windows : List (Window bytes)) : Except GlobalStateError Output := do
  let state ← GeneralBorrowProtectedSiblingPartial.operation bytes windows
  pure ⟨state,execute state.tree state.global.protectedTags state.tags,state.global.endCall state.frame⟩

structure History (bytes : UInt64) (windows : List (Window bytes)) where
  output : Output
  actual : operation bytes windows = .ok output
  released : AllReleased output.generated.tree output.generated.global.protectedTags output.generated.tags
  coherent : Every (fun location => GeneralBorrowExposureCardinality.LocationCoherent output.tree location output.ended.protectedTags) output.tree.locations
  rootNode : TreeNode
  rootPresent : output.tree.nodeAt GeneralBorrowFullSharedSeed.root = some rootNode
  rootTag : output.tree.indexOfTag BorTag.one = some GeneralBorrowFullSharedSeed.root
  depth : GeneralBorrowExposure.ParentDepth output.tree.nodes
  children : GeneralBorrowGraph.ChildNodes output.tree
  covered : GeneralBorrowGraph.RootsCover output.tree
  roots : output.tree.roots = #[GeneralBorrowFullSharedSeed.root]
  hidden : GeneralBorrowFreshProtectedSlotFlags.Unexposed output.tree
  nodes : output.tree.nodes.size = windows.length+1
  allocator : GeneralBorrowGcAllocator.Invariant output.tree
  vacant : GeneralBorrowGcVacantClean.VacantClean output.tree
  well : output.tree.locations.WellFormed
  capacity : output.tree.locations.size = Size.ofBytes bytes
  below : GeneralBorrowProtectedSiblingGenerationBounds.KeysBelow output.tree.tagMapping output.ended.nextPointerTag.value.toNat
  empty : output.ended.protectedTags = {}
  owned : Every (GeneralBorrowRange.LocationOwned output.tree output.ended.protectedTags GeneralBorrowFullSharedSeed.root .Write) output.tree.locations

/-- Arbitrary positive overlapping window chronology forms every initial borrow
fact after all actual releases and endCall, from allocation and numeric room. -/
def generate (bytes : UInt64) (nonzero : bytes ≠ 0) (windows : List (Window bytes))
    (room : windows.length+10 ≤ 4294967295) : History bytes windows := by
  have reserve : windows.length+2 ≤ 4294967295 := by omega
  let ready := Classical.choice (GeneralBorrowProtectedSiblingPartial.generate bytes nonzero windows reserve)
  have mapped : Tags ready.input.tree ready.state.global.protectedTags ready.state.tags := by
    intro tag member
    obtain ⟨descriptor⟩ := ready.descriptors tag member
    have lookup : ready.input.tree.indexOfTag tag = some descriptor.index := by
      simpa only [BorrowTree.indexOfTag,descriptor.tagged] using ready.allocator.nodeTags descriptor.index descriptor.node descriptor.present
    exact ⟨descriptor.index,descriptor.node,descriptor.present,lookup,descriptor.tagged,ready.held tag member⟩
  have fits : ready.input.tree.nodes.data.size ≤ 4294967296 := by have aligned := ready.input.aligned;have room := ready.input.fits;omega
  have stable : Every (GeneralBorrowProtectedSiblingReleaseStable.ForTags ready.state.tags.dropLast ready.input.tree) ready.input.tree.locations := by
    intro position valid index node present exposed member
    rw [ready.hidden index node present] at exposed
    cases exposed
  have cache := GeneralBorrowProtectedSiblingReleaseHistory.complete ready.input.tree ready.state.global.protectedTags ready.state.tags ready.input.parent
    ready.distinct fits ready.input.depth ready.input.children ready.roots ready.input.covered ready.allocator.nodeTags mapped ready.readable ready.coherent stable
  have readable := GeneralBorrowProtectedReleaseHistory.run ready.input.tree ready.state.global.protectedTags ready.state.tags ready.input.parent
    fits ready.input.depth ready.input.children ready.roots ready.input.covered mapped ready.readable
  have unique := GeneralBorrowProtectedSiblingRootUniqueHistory.unique ready.input.tree ready.state.global.protectedTags ready.state.tags ready.input.parent
    fits ready.input.depth ready.input.children ready.roots ready.input.covered mapped ready.input.parentNode ready.input.parentPresent ready.readable ready.rootUnique
  have clean : GeneralBorrowGcVacantClean.VacantClean ready.input.tree := by
    intro query missing position valid
    exact (ready.physical position valid).vacant query missing
  have vacant := GeneralBorrowProtectedSiblingVacantHistory.vacant ready.input.tree ready.state.global.protectedTags ready.state.tags ready.input.parent
    fits ready.input.depth ready.input.children ready.roots ready.input.covered mapped ready.readable clean
  let output : Output := ⟨ready.state,execute ready.input.tree ready.state.global.protectedTags ready.state.tags,ready.state.global.endCall ready.state.frame⟩
  have actual : operation bytes windows = .ok output := by
    simp only [operation,ready.actual,Except.bind,bind,pure,Except.pure]
    change Except.ok (⟨ready.state,execute ready.state.tree ready.state.global.protectedTags ready.state.tags,ready.state.global.endCall ready.state.frame⟩ : Output) =
      .ok ⟨ready.state,execute ready.input.tree ready.state.global.protectedTags ready.state.tags,ready.state.global.endCall ready.state.frame⟩
    rw [ready.tree]
  have frame : output.tree = {ready.input.tree with locations := output.tree.locations} :=
    GeneralBorrowProtectedSiblingWindowResources.frame ready.input.tree ready.state.global.protectedTags ready.state.tags
  have geometry := GeneralBorrowProtectedSiblingWindowResources.geometry ready.input.tree ready.state.global.protectedTags ready.state.tags ready.input.well
  have ended : output.ended.protectedTags = {} := GeneralBorrowProtectedSiblingWindowTable.end_call ready.state.global ready.state.frame
    (GeneralBorrowProtectedSiblingPartialTable.generated bytes windows ready.state ready.actual)
  have cleanup := GeneralBorrowProtectedReleaseCacheHistory.pending_end_call ready.state.global ready.state.frame
    GeneralBorrowProtectedSiblingGenerationWindowSeed.allocation ready.state.tags (by simp [ready.frame])
  rw [←cleanup] at cache
  have owner : Every (GeneralBorrowRange.LocationOwned output.tree output.ended.protectedTags GeneralBorrowFullSharedSeed.root .Write) output.tree.locations := by
    rw [ended,←ready.parent]
    intro position valid
    apply GeneralBorrowProtectedSiblingRootOwned.location output.tree _ ready.state.global.protectedTags ready.input.parent ready.input.parentNode
      (by rw [frame];exact ready.input.parentPresent) (by rw [frame];exact ready.roots) (by rw [frame];exact ready.input.covered)
      (by rw [frame];exact ready.input.depth)
    · exact readable.2.2 position valid
    · exact unique position valid
  exact {
    output := output,actual := actual,released := by rw [←ready.tree];exact cache.1,coherent := cache.2,
    rootNode := ready.input.parentNode,
    rootPresent := by rw [frame];change ready.input.tree.nodeAt GeneralBorrowFullSharedSeed.root = _;simpa only [ready.parent] using ready.input.parentPresent,
    rootTag := by rw [frame];change ready.input.tree.tagMapping.get BorTag.one = _;simpa only [ready.parentTag,ready.parent] using ready.input.parentTagPresent,
    depth := by rw [frame];exact ready.input.depth,children := by rw [frame];exact ready.input.children,
    covered := by rw [frame];exact ready.input.covered,roots := by rw [frame];exact ready.roots.trans (congrArg (fun root => #[root]) ready.parent),
    hidden := by rw [frame];exact ready.hidden,nodes := by rw [frame];exact ready.nodes,
    allocator := by rw [frame];exact ⟨ready.allocator.pool,ready.allocator.accounting,ready.allocator.unique,ready.allocator.nodeTags⟩,vacant := vacant,well := geometry.1,capacity := geometry.2.trans ready.capacity,
    below := by rw [frame];exact ready.mapBelow,empty := ended,owned := owner }
end
end DuplicatePrefix.GeneralBorrowProtectedSiblingPartialFunctionHistory
