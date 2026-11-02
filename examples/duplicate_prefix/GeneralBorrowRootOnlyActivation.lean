import duplicate_prefix.GeneralBorrowRootOnlyChildCache
import duplicate_prefix.GeneralBorrowDefaultActivatedStage
namespace DuplicatePrefix.GeneralBorrowRootOnlyActivation
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowRootOnlyExposureExact DuplicatePrefix.GeneralBorrowRootOnlyRangeCache
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowPartitionState
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- An actual Default reservation followed by the actual child Write preserves
the original root's exact cache, Unique storage and exposure flag. -/
theorem raw (tree : BorrowTree) (root : UniIndex) (capacity : UInt64) (s : State tree root capacity)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+5 ≤ 4294967295)
    (cache : ExposedCache) (only : RootOnly tree root) (initial : Every (LocationInvariant cache root) tree.locations) :
    let after := (GeneralBorrowDefaultActivation.write tree s.node.tag tag offset len).tree
    RootOnly after root ∧ Every (LocationInvariant cache root) after.locations ∧
      (after.nodes.get root).map TreeNode.isExposed = (tree.nodes.get root).map TreeNode.isExposed := by
  dsimp only
  obtain ⟨formed,before,index,node,rootTag,lookup,present,tagged,parent,typed⟩ :=
    GeneralBorrowDefaultChildState.prepare tree root capacity s offset len nonzero bounds tag fresh room
  have reserved := GeneralBorrowRootOnlyPositiveConstructors.reserve tree root capacity s offset len nonzero bounds tag fresh room cache only initial
  have flag := GeneralBorrowRootOnlyConstructorFlags.reserve tree root capacity s offset len nonzero bounds tag fresh room
  have owned := GeneralBorrowDefaultChildState.child_every _ root index capacity before node present parent typed
  have written := GeneralBorrowRootOnlyChildCache.ranged _ root index capacity before node present parent tag lookup offset len bounds .Write reserved.1 cache reserved.2 owned
  exact ⟨written.1,written.2.1,written.2.2.trans flag⟩

/-- The complete actual root Read→Default reservation→child Write stage is
cache-coherent in the root-only exposure protocol, with no operation-success or
intermediate cache assumption. -/
theorem stage (tree : BorrowTree) (root : UniIndex) (capacity : UInt64) (s : State tree root capacity)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+5 ≤ 4294967295)
    (cache : ExposedCache) (only : RootOnly tree root) (initial : Every (LocationInvariant cache root) tree.locations) :
    let after := (GeneralBorrowDefaultActivatedStage.operation tree s.node.tag tag offset len).tree
    RootOnly after root ∧ Every (LocationInvariant cache root) after.locations ∧
      (after.nodes.get root).map TreeNode.isExposed = (tree.nodes.get root).map TreeNode.isExposed := by
  dsimp only
  have read := GeneralBorrowPartitionState.access tree root capacity s offset len .Read bounds
  have readFrame := GeneralBorrowRootOnlyStageFrames.access tree root capacity s offset len .Read bounds cache only initial
  obtain ⟨⟨prepared,tagged⟩⟩ := read.2.1
  have readyFresh : GeneralBorrowTagMap.Fresh (GeneralBorrowPartitionState.operation tree s.node.tag offset len .Read).tree.tagMapping tag := by
    rw [read.2.2.2];exact fresh
  have readyRoom : (GeneralBorrowPartitionState.operation tree s.node.tag offset len .Read).tree.nodes.size+5 ≤ 4294967295 := by
    rw [read.2.2.1];exact room
  have activated := raw _ root capacity prepared offset len nonzero bounds tag readyFresh readyRoom cache readFrame.1 readFrame.2.1
  rw [tagged] at activated
  exact ⟨activated.1,activated.2.1,activated.2.2.trans readFrame.2.2⟩

end DuplicatePrefix.GeneralBorrowRootOnlyActivation
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowRootOnlyActivation." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved root-only activation dependency {dependency}"
