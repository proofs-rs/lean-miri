import duplicate_prefix.GeneralBorrowRecursiveSharedHistory
import duplicate_prefix.GeneralBorrowReusableGeneration
import duplicate_prefix.GeneralBorrowPartitionState

namespace DuplicatePrefix.GeneralBorrowRecursiveSharedGeneration
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowRecursiveSharedHistory DuplicatePrefix.GeneralBorrowFreshMixedChild
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- A generated partition state initializes recursive child-source generation
on any in-bounds positive subrange. All graph/resource/ownership fields are
copied from proved data; no successful operation is an input. -/
def of_partition (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : GeneralBorrowPartitionState.State tree root capacity) (offset len : UInt64)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat) : State root offset len where
  tree := tree
  resources := {
    depth := GeneralBorrowStarCertificates.depth tree root s.node s.star
    children := GeneralBorrowStarCertificates.children tree root s.node s.star
    covered := GeneralBorrowStarCertificates.covered tree root s.node s.star s.roots
    roots := s.roots,allocator := s.allocator,clean := s.clean,well := s.well,room := s.room }
  parent := root
  node := s.node
  present := s.star.present
  protections := {}
  writable := fun _ => true
  bounds := by rw [s.capacity];exact bounds
  owned := by
    intro position valid positive lower upper
    exact write_combined tree _ {} root (s.owned position valid)

/-- The real allocation constructor initializes the recursive-chain data. The
extra distinct tag is a resource used only to instantiate the earlier seed API;
it is not inserted into the initial BorrowTree. -/
def allocation (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag resourceTag : BorTag)
    (different : rootTag ≠ resourceTag) : State GeneralBorrowFullSharedSeed.root 0 capacity :=
  of_partition (BorrowTree.new rootTag (Size.ofBytes capacity)) GeneralBorrowFullSharedSeed.root capacity
    (GeneralBorrowPartitionState.of_reusable _ GeneralBorrowFullSharedSeed.root capacity
      (GeneralBorrowReusableGeneration.seed capacity nonzero rootTag resourceTag different)) 0 capacity (by simp)

theorem allocation_height (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag resourceTag : BorTag)
    (different : rootTag ≠ resourceTag) : height (allocation capacity nonzero rootTag resourceTag different) = 1 := by
  let location : LocationTree := ⟨⟨#[]⟩,{}⟩
  have path : (source_normal_projection (BorrowTree.new rootTag (Size.ofBytes capacity)) location {}).topology.ancestorPath
      GeneralBorrowFullSharedSeed.root.toNat = [GeneralBorrowFullSharedSeed.root.toNat] :=
    GeneralBorrowSharedProfileParentRead.parent_path (GeneralBorrowFullSharedSeed.input capacity nonzero rootTag resourceTag different) location {} rfl
  have count := congrArg List.length path
  simpa only [height,allocation,of_partition,List.length_singleton] using count

/-- Actual allocation followed by an arbitrary finite chain of successive
shared descendants. Both operations at every stage complete; graph/allocator/
Clean, mixed local ownership and active ranges are derived. The source ancestor
path grows by exactly the chain length. This does not claim mutable ownership
of the final shared descendant or a whole-function invocation from that tag. -/
theorem generate (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag resourceTag : BorTag)
    (different : rootTag ≠ resourceTag) (steps : List (BorTag × Bool))
    (unique : (steps.map Prod.fst).Nodup) (rootUnused : rootTag ∉ steps.map Prod.fst)
    (room : 1+steps.length+4 ≤ 4294967295) :
    let initial := allocation capacity nonzero rootTag resourceTag different
    ∃ final : State GeneralBorrowFullSharedSeed.root 0 capacity,
      Run nonzero initial steps final ∧
      height final = steps.length+1 ∧
      final.tree.nodes.size ≤ 1+steps.length ∧
      (steps ≠ [] → GeneralBorrowFreshActiveWithin.ActiveWithin final.tree final.parent .Read 0 capacity) ∧
      (∀ tag, tag ∉ steps.map Prod.fst → rootTag ≠ tag → GeneralBorrowTagMap.Fresh final.tree.tagMapping tag) := by
  dsimp only
  let initial := allocation capacity nonzero rootTag resourceTag different
  have seedSize : initial.tree.nodes.size = 1 := by
    change (GeneralBorrowFullSharedSeed.tree capacity nonzero rootTag).nodes.size = 1
    rw [GeneralBorrowFullSharedSeed.tree_eq];rfl
  have fresh : ∀ tag ∈ steps.map Prod.fst, GeneralBorrowTagMap.Fresh initial.tree.tagMapping tag := by
    intro tag member
    exact GeneralBorrowReusableGeneration.seed_fresh capacity nonzero rootTag tag (fun same => rootUnused (same ▸ member))
  obtain ⟨final,history,bound,future⟩ := GeneralBorrowRecursiveSharedHistory.generate initial nonzero steps unique fresh (by rw [seedSize];exact room)
  refine ⟨final,history,?_,?_,?_,?_⟩
  · have depth := history.height
    have start := allocation_height capacity nonzero rootTag resourceTag different
    change height initial = 1 at start
    omega
  · simpa only [seedSize] using bound
  · intro nonempty
    simpa only [UInt64.zero_add] using history.final_active nonempty
  · intro tag unused notRoot
    exact future tag unused (GeneralBorrowReusableGeneration.seed_fresh capacity nonzero rootTag tag notRoot)

end DuplicatePrefix.GeneralBorrowRecursiveSharedGeneration
