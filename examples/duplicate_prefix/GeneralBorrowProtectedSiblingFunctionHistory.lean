import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationWindowFalse
import duplicate_prefix.GeneralBorrowProtectedSiblingWindowResources
import duplicate_prefix.GeneralBorrowProtectedSiblingWindowRootOwned
import duplicate_prefix.GeneralBorrowProtectedSiblingWindowTable
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingFunctionHistory
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProtectedSiblingGenerationWindow GeneralBorrowProtectedReleaseHistory GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
noncomputable section

structure History (bytes : UInt64) (n : Nat) where
  output : GeneralBorrowProtectedSiblingWindowLifetimes.Output
  actual : GeneralBorrowProtectedSiblingWindowLifetimes.operation bytes (List.replicate n false) = .ok output
  rootNode : TreeNode
  rootPresent : output.tree.nodeAt GeneralBorrowFullSharedSeed.root = some rootNode
  rootTag : output.tree.indexOfTag BorTag.one = some GeneralBorrowFullSharedSeed.root
  depth : GeneralBorrowExposure.ParentDepth output.tree.nodes
  children : GeneralBorrowGraph.ChildNodes output.tree
  covered : GeneralBorrowGraph.RootsCover output.tree
  roots : output.tree.roots = #[GeneralBorrowFullSharedSeed.root]
  hidden : GeneralBorrowFreshProtectedSlotFlags.Unexposed output.tree
  nodes : output.tree.nodes.size = n+1
  allocator : GeneralBorrowGcAllocator.Invariant output.tree
  vacant : GeneralBorrowGcVacantClean.VacantClean output.tree
  well : output.tree.locations.WellFormed
  capacity : output.tree.locations.size = Size.ofBytes bytes
  below : GeneralBorrowProtectedSiblingGenerationBounds.KeysBelow output.tree.tagMapping output.ended.nextPointerTag.value.toNat
  empty : output.ended.protectedTags = {}
  owned : Every (GeneralBorrowRange.LocationOwned output.tree output.ended.protectedTags GeneralBorrowFullSharedSeed.root .Write) output.tree.locations

/-- Actual allocation and n simultaneously live protected siblings, then every
real release and endCall. Borrow ownership and resources are outputs. -/
def generate (bytes : UInt64) (nonzero : bytes ≠ 0) (n : Nat) (room : n+10 ≤ 4294967295) : History bytes n := by
  have reserve : (List.replicate n false).length+2 ≤ 4294967295 := by simp only [List.length_replicate];omega
  let ready := Classical.choice (GeneralBorrowProtectedSiblingGenerationWindow.generate bytes nonzero (List.replicate n false) reserve)
  let output : GeneralBorrowProtectedSiblingWindowLifetimes.Output := ⟨ready.state,
    execute ready.input.tree ready.state.global.protectedTags ready.state.tags,ready.state.global.endCall ready.state.frame⟩
  have actual : GeneralBorrowProtectedSiblingWindowLifetimes.operation bytes (List.replicate n false) = .ok output := by
    simp only [GeneralBorrowProtectedSiblingWindowLifetimes.operation,ready.actual,Except.bind,bind,pure,Except.pure]
    change Except.ok (⟨ready.state,execute ready.state.tree ready.state.global.protectedTags ready.state.tags,ready.state.global.endCall ready.state.frame⟩ : GeneralBorrowProtectedSiblingWindowLifetimes.Output) = .ok ⟨ready.state,execute ready.input.tree ready.state.global.protectedTags ready.state.tags,ready.state.global.endCall ready.state.frame⟩
    rw [ready.tree]
  have resources := GeneralBorrowProtectedSiblingWindowResources.formed bytes nonzero (List.replicate n false) reserve
  have owner := GeneralBorrowProtectedSiblingWindowRootOwned.formed bytes nonzero (List.replicate n false) reserve
  have empty := GeneralBorrowProtectedSiblingWindowTable.formed bytes nonzero (List.replicate n false) reserve
  rw [actual] at resources owner empty
  have flags := GeneralBorrowProtectedSiblingGenerationWindowFalse.formed bytes nonzero n (by simpa only [List.length_replicate] using reserve) ready
  have frame : output.tree = {ready.input.tree with locations := output.tree.locations} :=
    GeneralBorrowProtectedSiblingWindowResources.frame ready.input.tree ready.state.global.protectedTags ready.state.tags
  exact {
    output := output,actual := actual,rootNode := ready.input.parentNode,
    rootPresent := by rw [frame];change ready.input.tree.nodeAt GeneralBorrowFullSharedSeed.root = _;simpa only [ready.parent] using ready.input.parentPresent,
    rootTag := by rw [frame];change ready.input.tree.tagMapping.get BorTag.one = _;simpa only [ready.parentTag,ready.parent] using ready.input.parentTagPresent,
    depth := Classical.choice resources.2.2.2.2.1,children := resources.2.2.2.2.2.1,covered := resources.2.2.2.2.2.2.1,
    roots := resources.2.2.2.2.2.2.2.1,hidden := by rw [frame];exact flags.1,
    nodes := by rw [frame];exact flags.2,allocator := resources.1,vacant := resources.2.1,well := resources.2.2.1,
    capacity := resources.2.2.2.1,below := resources.2.2.2.2.2.2.2.2,empty := empty,owned := owner }
end
end DuplicatePrefix.GeneralBorrowProtectedSiblingFunctionHistory
