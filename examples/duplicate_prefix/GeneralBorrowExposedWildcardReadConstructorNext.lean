import duplicate_prefix.GeneralBorrowExposedWildcardStoredRead
import duplicate_prefix.GeneralBorrowWildcardConstructorNextRead
namespace DuplicatePrefix.GeneralBorrowExposedWildcardReadConstructorNext
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.RangeMapNonempty
open DuplicatePrefix.GeneralBorrowWildcardLeaf DuplicatePrefix.GeneralBorrowExposureCardinality
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Full positive wildcard Read, protected wildcard reborrow, then actual
concrete Read on every installed byte row. All stages are the interpreter's
real operations. Initial exposed leaf support and stored rows form the first
Read; initial allocator/tag/byte geometry forms the new root; initial coherent
counters derive the next Local/Either classifications, including protected
Unique extras. No intermediate success, coherence or ownership is assumed.
The initial partition is homogeneous over the whole positive allocation. -/
theorem append (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (head : UniIndex) (headNode : TreeNode) (extras : List UniIndex) (nodes : UniIndex → TreeNode)
    (states : UniIndex → LocationState) (tag : BorTag) (capacity : UInt64) (nonzero : capacity ≠ 0)
    (locations : tree.locations = homogeneous capacity location)
    (roots : tree.roots = (head::extras).toArray)
    (headPresent : tree.nodes.get head = some headNode) (headLeaf : headNode.children = #[])
    (headExposed : headNode.isExposed = true) (headStored : location.perms.get head = some unique)
    (headBound : headNode.tag.value ≤ tag.value)
    (data : ∀ root ∈ extras, tree.nodes.get root = some (nodes root) ∧ (nodes root).children = #[] ∧
      (nodes root).isExposed = true ∧ (nodes root).tag.value ≤ tag.value ∧
      location.perms.get root = some (states root) ∧ supports (effective location protections root (nodes root)) .Read = true)
    (coherent : LocationCoherent tree location protections)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (noFree : tree.tagMapping.deassigned.back? = none)
    (aligned : tree.tagMapping.mapping.size = tree.nodes.data.size) (short : tree.nodes.size+1 < 65536) :
    let read := tree.performBorrowAccessRange .wildcard Size.ZERO (Size.ofBytes capacity) .Read protections .VisitChildrenOfAccessed
    let inserted := read.tree.newChild Size.ZERO .wildcard tag
      (DedupRangeMap.new (Size.ofBytes capacity) ⟨.ReservedFrz false,true,.None⟩) (.ReservedFrz false) true
    let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    read.status = .Completed ∧ inserted.outcome = .ok () ∧
      GeneralRangeMapOrigins.OwnedOn
        (fun location => ∀ range : ByteRange,
          source_access_status (source_tree_access_at inserted.tree location (some index) .Read protections .VisitChildrenOfAccessed range) = none ∧
          LocationCoherent inserted.tree (source_access_location
            (source_tree_access_at inserted.tree location (some index) .Read protections .VisitChildrenOfAccessed range)) protections)
        0 capacity inserted.tree.locations := by
  have read := GeneralBorrowExposedWildcardStoredRead.ranged tree location protections head headNode extras nodes states capacity nonzero
    locations roots headPresent headLeaf headExposed headStored coherent (by omega)
    (fun root member => ⟨(data root member).1,(data root member).2.1,(data root member).2.2.1,
      (data root member).2.2.2.2.1,(data root member).2.2.2.2.2⟩)
  have well : tree.locations.WellFormed := by
    rw [locations]
    simp [homogeneous,DedupRangeMap.WellFormed,UInt64.pos_iff_ne_zero.mpr nonzero]
  have bounds : (0 : UInt64).toNat+capacity.toNat ≤ tree.locations.size.bytes.toNat := by
    rw [locations]
    simp [homogeneous,DedupRangeMap.size,Size.ofBytes]
  have everyCoherent : GeneralRangeMapState.Every (fun location => LocationCoherent tree location protections) tree.locations := by
    intro position valid
    have same : position = 0 := by rw [locations] at valid;change position < 1 at valid;omega
    subst position
    simpa [locations,homogeneous] using coherent
  have profile : GeneralRangeMapState.Every (GeneralBorrowWildcardConstructorNextRead.Profile protections head extras nodes) tree.locations := by
    intro position valid
    have same : position = 0 := by rw [locations] at valid;change position < 1 at valid;omega
    subst position
    refine ⟨?_,?_⟩
    · simpa [locations,homogeneous] using headStored
    · intro root member
      simpa [locations,homogeneous] using (data root member).2.2.2.2.2
  have next := GeneralBorrowWildcardConstructorNextRead.append tree depth protections head headNode extras nodes tag 0 capacity roots
    headPresent headLeaf headExposed headBound
    (fun root member => ⟨(data root member).1,(data root member).2.1,(data root member).2.2.1,(data root member).2.2.2.1⟩)
    fresh noFree aligned short nonzero well bounds everyCoherent profile
  dsimp only
  rw [read.2]
  exact ⟨read.1,next.1,by simpa only [UInt64.zero_add,Size.ZERO,Size.ofBytes] using next.2⟩
end DuplicatePrefix.GeneralBorrowExposedWildcardReadConstructorNext
