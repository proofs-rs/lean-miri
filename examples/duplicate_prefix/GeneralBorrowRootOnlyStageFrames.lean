import duplicate_prefix.GeneralBorrowRootOnlyConstructorFlags
import duplicate_prefix.GeneralBorrowPartitionSharedStage
import duplicate_prefix.GeneralBorrowPartitionDefaultStage
import duplicate_prefix.GeneralBorrowZeroSharedStage
import duplicate_prefix.GeneralBorrowZeroDefaultStage
namespace DuplicatePrefix.GeneralBorrowRootOnlyStageFrames
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowRootOnlyExposureExact DuplicatePrefix.GeneralBorrowRootOnlyRangeCache
open DuplicatePrefix.GeneralBorrowPartitionState DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- Exact location invariants and root flags survive the actual partitioned
root Read/Write operation, including its physical interval preparation. -/
theorem access (tree : BorrowTree) (root : UniIndex) (bytes : UInt64) (s : State tree root bytes)
    (offset len : UInt64) (kind : AccessKind) (bounds : offset.toNat+len.toNat ≤ bytes.toNat)
    (cache : ExposedCache) (only : RootOnly tree root)
    (initial : Every (LocationInvariant cache root) tree.locations) :
    let after := (GeneralBorrowPartitionState.operation tree s.node.tag offset len kind).tree
    RootOnly after root ∧ Every (LocationInvariant cache root) after.locations ∧
      (after.nodes.get root).map TreeNode.isExposed = (tree.nodes.get root).map TreeNode.isExposed := by
  dsimp only
  have owned : Every (GeneralBorrowRange.LocationOwned tree {} root kind) tree.locations := by
    intro position valid
    obtain ⟨forest,owner⟩ := s.owned position valid
    exact ⟨forest,GeneralBorrowRangePreserves.owned_for_access _ root.toNat kind .Write (by intro impossible;cases impossible) owner⟩
  have request : (Size.ofBytes offset).bytes.toNat+(Size.ofBytes len).bytes.toNat ≤ tree.locations.size.bytes.toNat := by
    rw [s.capacity];exact bounds
  have facts := ranged tree s.node.tag root s.node (Size.ofBytes offset) (Size.ofBytes len) kind {} .VisitChildrenOfAccessed cache
    (by have room := s.room;change tree.nodes.data.size+4 ≤ _ at room;omega)
    (GeneralBorrowStarCertificates.depth tree root s.node s.star)
    (GeneralBorrowStarCertificates.children tree root s.node s.star) s.star.present s.roots
    (GeneralBorrowStarCertificates.covered tree root s.node s.star s.roots)
    (s.allocator.nodeTags root s.node s.star.present) s.well only owned initial request
  have frame := GeneralBorrowFreshReadFrame.frame tree (.concrete s.node.tag) (Size.ofBytes offset) (Size.ofBytes len)
    kind {} .VisitChildrenOfAccessed
  have nodes : (GeneralBorrowPartitionState.operation tree s.node.tag offset len kind).tree.nodes = tree.nodes := by
    simpa only [GeneralBorrowPartitionState.operation,BorrowTree.performNormalAccessRange] using congrArg BorrowTree.nodes frame
  refine ⟨?_,facts.2,?_⟩
  · intro index node present exposed
    rw [nodes] at present
    exact only index node present exposed
  · rw [nodes]

/-- The actual root Read followed by the actual Shared positive
constructor preserves the root-only protocol's exact cache and root flag. -/
theorem shared (tree : BorrowTree) (root : UniIndex) (bytes : UInt64) (s : State tree root bytes)
    (offset : UInt64) (len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ bytes.toNat) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+5 ≤ 4294967295)
    (cache : ExposedCache) (only : RootOnly tree root)
    (initial : Every (LocationInvariant cache root) tree.locations) :
    let after := (GeneralBorrowPartitionSharedStage.operation tree s.node.tag tag offset len).tree
    RootOnly after root ∧ Every (LocationInvariant cache root) after.locations ∧
      (after.nodes.get root).map TreeNode.isExposed = (tree.nodes.get root).map TreeNode.isExposed := by
  dsimp only
  have read := GeneralBorrowPartitionState.access tree root bytes s offset len .Read (by simpa using bounds)
  have readFrame := access tree root bytes s offset len .Read (by simpa using bounds) cache only initial
  obtain ⟨⟨prepared,tagged⟩⟩ := read.2.1
  have readyFresh : GeneralBorrowTagMap.Fresh (GeneralBorrowPartitionState.operation tree s.node.tag offset len .Read).tree.tagMapping tag := by
    rw [read.2.2.2];exact fresh
  have readyRoom : (GeneralBorrowPartitionState.operation tree s.node.tag offset len .Read).tree.nodes.size+5 ≤ 4294967295 := by
    rw [read.2.2.1];exact room
  have constructed := GeneralBorrowRootOnlyPositiveConstructors.shared _ root bytes prepared offset len nonzero bounds tag readyFresh readyRoom cache readFrame.1 readFrame.2.1
  have flag := GeneralBorrowRootOnlyConstructorFlags.shared _ root bytes prepared offset len nonzero bounds tag readyFresh readyRoom
  rw [tagged] at constructed flag
  exact ⟨constructed.1,constructed.2,flag.trans readFrame.2.2⟩

/-- The actual root Read followed by the actual Default positive
constructor preserves the root-only protocol's exact cache and root flag. -/
theorem reserve (tree : BorrowTree) (root : UniIndex) (bytes : UInt64) (s : State tree root bytes)
    (offset : UInt64) (len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ bytes.toNat) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+5 ≤ 4294967295)
    (cache : ExposedCache) (only : RootOnly tree root)
    (initial : Every (LocationInvariant cache root) tree.locations) :
    let after := (GeneralBorrowPartitionDefaultStage.operation tree s.node.tag tag offset len).tree
    RootOnly after root ∧ Every (LocationInvariant cache root) after.locations ∧
      (after.nodes.get root).map TreeNode.isExposed = (tree.nodes.get root).map TreeNode.isExposed := by
  dsimp only
  have read := GeneralBorrowPartitionState.access tree root bytes s offset len .Read (by simpa using bounds)
  have readFrame := access tree root bytes s offset len .Read (by simpa using bounds) cache only initial
  obtain ⟨⟨prepared,tagged⟩⟩ := read.2.1
  have readyFresh : GeneralBorrowTagMap.Fresh (GeneralBorrowPartitionState.operation tree s.node.tag offset len .Read).tree.tagMapping tag := by
    rw [read.2.2.2];exact fresh
  have readyRoom : (GeneralBorrowPartitionState.operation tree s.node.tag offset len .Read).tree.nodes.size+5 ≤ 4294967295 := by
    rw [read.2.2.1];exact room
  have constructed := GeneralBorrowRootOnlyPositiveConstructors.reserve _ root bytes prepared offset len nonzero bounds tag readyFresh readyRoom cache readFrame.1 readFrame.2.1
  have flag := GeneralBorrowRootOnlyConstructorFlags.reserve _ root bytes prepared offset len nonzero bounds tag readyFresh readyRoom
  rw [tagged] at constructed flag
  exact ⟨constructed.1,constructed.2,flag.trans readFrame.2.2⟩

/-- The actual root Read followed by the actual Shared empty
constructor preserves the root-only protocol's exact cache and root flag. -/
theorem zero_shared (tree : BorrowTree) (root : UniIndex) (bytes : UInt64) (s : State tree root bytes)
    (offset : UInt64) (bounds : offset.toNat ≤ bytes.toNat) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+5 ≤ 4294967295)
    (cache : ExposedCache) (only : RootOnly tree root)
    (initial : Every (LocationInvariant cache root) tree.locations) :
    let after := (GeneralBorrowZeroSharedStage.operation tree s.node.tag tag offset).tree
    RootOnly after root ∧ Every (LocationInvariant cache root) after.locations ∧
      (after.nodes.get root).map TreeNode.isExposed = (tree.nodes.get root).map TreeNode.isExposed := by
  dsimp only
  have read := GeneralBorrowPartitionState.access tree root bytes s offset 0 .Read (by simpa using bounds)
  have readFrame := access tree root bytes s offset 0 .Read (by simpa using bounds) cache only initial
  obtain ⟨⟨prepared,tagged⟩⟩ := read.2.1
  have readyFresh : GeneralBorrowTagMap.Fresh (GeneralBorrowPartitionState.operation tree s.node.tag offset 0 .Read).tree.tagMapping tag := by
    rw [read.2.2.2];exact fresh
  have readyRoom : (GeneralBorrowPartitionState.operation tree s.node.tag offset 0 .Read).tree.nodes.size+5 ≤ 4294967295 := by
    rw [read.2.2.1];exact room
  have constructed := GeneralBorrowRootOnlyZeroConstructors.shared _ root bytes prepared tag readyFresh readyRoom offset cache readFrame.1 readFrame.2.1
  have flag := GeneralBorrowRootOnlyConstructorFlags.zero_shared _ root bytes prepared tag readyFresh readyRoom offset
  rw [tagged] at constructed flag
  exact ⟨constructed.1,constructed.2,flag.trans readFrame.2.2⟩

/-- The actual root Read followed by the actual Default empty
constructor preserves the root-only protocol's exact cache and root flag. -/
theorem zero_reserve (tree : BorrowTree) (root : UniIndex) (bytes : UInt64) (s : State tree root bytes)
    (offset : UInt64) (bounds : offset.toNat ≤ bytes.toNat) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+5 ≤ 4294967295)
    (cache : ExposedCache) (only : RootOnly tree root)
    (initial : Every (LocationInvariant cache root) tree.locations) :
    let after := (GeneralBorrowZeroDefaultStage.operation tree s.node.tag tag offset).tree
    RootOnly after root ∧ Every (LocationInvariant cache root) after.locations ∧
      (after.nodes.get root).map TreeNode.isExposed = (tree.nodes.get root).map TreeNode.isExposed := by
  dsimp only
  have read := GeneralBorrowPartitionState.access tree root bytes s offset 0 .Read (by simpa using bounds)
  have readFrame := access tree root bytes s offset 0 .Read (by simpa using bounds) cache only initial
  obtain ⟨⟨prepared,tagged⟩⟩ := read.2.1
  have readyFresh : GeneralBorrowTagMap.Fresh (GeneralBorrowPartitionState.operation tree s.node.tag offset 0 .Read).tree.tagMapping tag := by
    rw [read.2.2.2];exact fresh
  have readyRoom : (GeneralBorrowPartitionState.operation tree s.node.tag offset 0 .Read).tree.nodes.size+5 ≤ 4294967295 := by
    rw [read.2.2.1];exact room
  have constructed := GeneralBorrowRootOnlyZeroConstructors.reserve _ root bytes prepared tag readyFresh readyRoom offset cache readFrame.1 readFrame.2.1
  have flag := GeneralBorrowRootOnlyConstructorFlags.zero_reserve _ root bytes prepared tag readyFresh readyRoom offset
  rw [tagged] at constructed flag
  exact ⟨constructed.1,constructed.2,flag.trans readFrame.2.2⟩

end DuplicatePrefix.GeneralBorrowRootOnlyStageFrames
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowRootOnlyStageFrames." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved root-only stage frame dependency {dependency}"
