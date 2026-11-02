import duplicate_prefix.GeneralBorrowGeneratedGcComplete
import duplicate_prefix.GeneralBorrowStarEntryData

namespace DuplicatePrefix.GeneralBorrowReusableStar
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGeneratedStarShape DuplicatePrefix.GeneralBorrowSharedGeneratorProfile
open DuplicatePrefix.GeneralBorrowGeneratedGcProfile DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

set_option autoImplicit false in
/-- Recurring single-root full-slice state. Sparse vacancies and a nonempty free
pool are permitted; no operation completion is a field. -/
structure State (tree : BorrowTree) (root : UniIndex) (capacity : UInt64) where
  node : TreeNode
  location : LocationTree
  nonzero : capacity ≠ 0
  star : Star tree root node
  roots : tree.roots = #[root]
  locations : tree.locations = RangeMapNonempty.homogeneous capacity location
  profile : Profile tree location root
  allocator : GeneralBorrowGcAllocator.Invariant tree
  room : tree.nodes.size+4 ≤ 4294967295

/-- The previously constructed append-history state embeds without assuming
anything about its subsequent GC or operations. -/
def of_generated (input : GeneralBorrowFreshMetadataChildShared.Input) (location : LocationTree)
    (good : GeneralBorrowFullSharedStep.State input location)
    (star : Star input.tree input.parent input.parentNode)
    (allocator : GeneralBorrowGcAllocator.Invariant input.tree)
    (room : input.tree.nodes.size+4 ≤ 4294967295) : State input.tree input.parent input.len :=
  ⟨input.parentNode,location,input.nonzero,star,good.roots,good.locations,good.profile,allocator,room⟩

/-- Homogeneous exact permissions imply the all-range GC policy, including
clean stored permissions at every vacant sparse slot. -/
theorem policy (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) : GeneralBorrowGcPermissionPolicy.Policy (expected root) tree := by
  constructor
  · intro query node present position valid
    have zero : position = 0 := by rw [s.locations] at valid;change position < 1 at valid;omega
    subst position
    have stored : s.location.perms.get query = some (expected root query) := by
      by_cases same : query = root
      · subst query;simpa only [expected,ite_true] using s.profile.rootStored
      · simpa only [expected,ite_false,same] using s.profile.shared query node present same
    simpa only [s.locations,RangeMapNonempty.homogeneous,Array.getElem_singleton] using stored
  · intro query vacant position valid
    have zero : position = 0 := by rw [s.locations] at valid;change position < 1 at valid;omega
    subst position
    simpa only [s.locations,RangeMapNonempty.homogeneous,Array.getElem_singleton] using s.profile.vacant query vacant

/-- Full production GC on a reusable state completes and forms another reusable
state. The live set is arbitrary: the star's sole root is structurally retained. -/
theorem collect (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) (live : Array BorTag) :
    (tree.removeUnreachableTags live).outcome = .ok () ∧
    Nonempty (State (tree.removeUnreachableTags live).tree root capacity) := by
  have notChild : root ∉ s.node.children.toList := by
    intro member;exact ((s.star.children root).mp member).1 rfl
  have leaves : ∀ index ∈ s.node.children.toList, ∃ child,
      tree.nodes.get index = some child ∧ child.children = #[] := by
    intro index member
    obtain ⟨different,child,present⟩ := (s.star.children index).mp member
    exact ⟨child,present,(s.star.leaves index child present different).2⟩
  have completion := GeneralBorrowGcStarComplete.complete tree root s.node live capacity s.location
    s.locations s.roots s.star.present s.star.distinct notChild leaves (children_bound tree root s.node s.star)
  obtain ⟨node,star⟩ := GeneralBorrowGcStarShape.preserves tree root s.node live s.star s.roots
  obtain ⟨location,locations⟩ := completion.2
  have frame := GeneralBorrowGcResourceFrame.preserves (fun i : Fin 0 => Fin.elim0 i) tree live (by intro i;exact Fin.elim0 i)
  have preserved := GeneralBorrowGcPermissionPolicy.preserves (expected root) tree live (policy tree root capacity s)
  have profiles := GeneralBorrowGeneratedGcProfile.profiles _ root node star.present preserved
  have profile : Profile (tree.removeUnreachableTags live).tree location root := by
    have stored := profiles 0 (by rw [locations];change 0 < 1;omega)
    simpa only [locations,RangeMapNonempty.homogeneous,Array.getElem_singleton] using stored
  refine ⟨completion.1,⟨⟨node,location,s.nonzero,star,frame.roots.trans s.roots,locations,profile,
    GeneralBorrowGcAllocatorFull.preserves tree live s.allocator,?_⟩⟩⟩
  rw [frame.capacity];exact s.room

/-- Retag-entry Data is formed internally from the recurring state and a fresh
input tag, regardless of the length or occupancy of its coherent free pool. -/
noncomputable def data (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) :
    GenericAsMutPtrEntryValidity.Data tree {} s.node.tag tag 0 capacity :=
  GeneralBorrowStarEntryData.data tree root s.node s.star s.roots capacity s.nonzero s.location
    s.locations s.profile s.allocator tag fresh s.room

end DuplicatePrefix.GeneralBorrowReusableStar
