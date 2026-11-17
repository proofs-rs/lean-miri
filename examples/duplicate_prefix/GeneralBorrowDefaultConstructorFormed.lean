import duplicate_prefix.GeneralBorrowStructuralHistoryDefault
import duplicate_prefix.GeneralBorrowStructuralHistorySifaConcrete
namespace DuplicatePrefix.GeneralBorrowDefaultConstructorFormed
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshDefaultChild (inside)
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Direct actual Default mutable construction preserves intrinsic structure and the
allocation-wide SIFA/vacant-Clean invariant, with arbitrary consistent free
pool. No exact ownership/exposure profile or successful operation is assumed.
Cache coherence, possible-state and source-capability transport are separate. -/
theorem construct (tree : BorrowTree) (protections : ProtectedTags)
    (initial : GeneralBorrowStructuralHistorySifaState.Formed tree protections)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (aligned : protections.contains newTag = false)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) inside) (.ReservedFrz false) false
    actual.outcome = .ok () ∧ GeneralBorrowStructuralHistorySifaState.Formed actual.tree protections ∧
    actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 := by
  have structural := GeneralBorrowStructuralHistoryDefault.construct tree initial.toState parentTag newTag parent parentNode
    tagged present fresh room offset len nonzero bounds
  have bounded : GeneralBorrowStructuralHistoryMixedConcrete.Bounded
      (DedupRangeMap.new (Size.ofBytes len) inside) (Size.ofBytes offset) tree.locations.size := by
    intro segment member start added
    have same : segment = ⟨⟨0,len⟩,inside⟩ := by
      simpa only [DedupRangeMap.iterAll,DedupRangeMap.new,Size.ofBytes,nonzero,beq_iff_eq,ite_false,
        List.mem_singleton] using member
    subst segment
    have zeroAdd : (Size.ofBytes 0).add (Size.ofBytes offset) = .ok (Size.ofBytes offset) := by simp [Size.add,Size.ofBytes]
    rw [zeroAdd] at added
    cases added
    simpa only [Size.ofBytes,UInt64.sub_zero] using bounds
  have consistentInside : ∀ segment ∈ (DedupRangeMap.new (Size.ofBytes len) inside).iterAll.toList,
      GeneralBorrowSifaPermissionConsistency.Consistent segment.data (protections.contains newTag) := by
    intro segment member
    have same : segment = ⟨⟨0,len⟩,inside⟩ := by
      simpa only [DedupRangeMap.iterAll,DedupRangeMap.new,Size.ofBytes,nonzero,beq_iff_eq,ite_false,
        List.mem_singleton] using member
    subst segment
    rw [aligned]
    exact ⟨.Read,rfl,Nat.le_refl _⟩
  have foreign : (Permission.ReservedFrz false).strongestIdempotentForeignAccess false = .Access .Read := rfl
  have profile := GeneralBorrowStructuralHistorySifaConcrete.profile tree initial.toState protections initial.profile
    parentTag parent parentNode tagged present newTag fresh room (.ReservedFrz false) .Read false rfl rfl foreign aligned
    (Size.ofBytes offset) (DedupRangeMap.new (Size.ofBytes len) inside) bounded consistentInside
  exact ⟨structural.1,⟨structural.2.1,profile⟩,structural.2.2.1,structural.2.2.2⟩

end DuplicatePrefix.GeneralBorrowDefaultConstructorFormed
