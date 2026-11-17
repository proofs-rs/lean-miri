import duplicate_prefix.GeneralBorrowReadProtectorRelease
import duplicate_prefix.GeneralBorrowProtectorCacheMap
namespace DuplicatePrefix.GeneralBorrowHiddenProtectorDropRuntime
open Miri Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowSifaPermissionConsistency GeneralBorrowLocationSifaConsistency
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- Protector weakening only increases the allowed foreign SIFA bound. -/
theorem scalar (state : LocationState) (before after : Bool)
    (weaken : after = true → before = true) (old : Consistent state before) : Consistent state after := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflict =>
    cases conflict <;> cases before <;> cases after <;>
      simp_all [Consistent,Permission.strongestIdempotentForeignAccess,IdempotentForeignAccess.rank]
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases before <;> cases after <;> simp_all [Consistent,Permission.strongestIdempotentForeignAccess]

/-- Raw physical SIFA/Clean data weakens with the actual protector table. -/
theorem profile (tree : BorrowTree) (location : LocationTree) (before after : ProtectedTags)
    (weaken : ∀ tag, after.contains tag = true → before.contains tag = true)
    (old : Profile tree location before) : Profile tree location after := by
  refine ⟨?_,old.vacant⟩
  intro index node present
  exact scalar _ _ _ (weaken node.tag) (old.present index node present)

/-- Exact singleton helper endCall retains complete runtime facts. All other
global protector entries survive unless they have this same tag. The actual
release operation must occur separately before this bookkeeping operation. -/
theorem end_call (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (allocation : AllocId) (tag : BorTag) (anchor : UniIndex) (node : TreeNode)
    (present : tree.nodeAt anchor = some node) (sameTag : node.tag = tag) (hidden : node.isExposed = false) :
    DuplicatePrefixBorrowContract.RuntimeFacts tree
      (global.endCall (({} : FrameState).addProtector allocation tag)) ∧
    (global.endCall (({} : FrameState).addProtector allocation tag)).protectedTags.contains tag = false ∧
    ∀ query, query ≠ tag →
      (global.endCall (({} : FrameState).addProtector allocation tag)).protectedTags.get query = global.protectedTags.get query := by
  have protectorEq : (global.endCall (({} : FrameState).addProtector allocation tag)).protectedTags =
      global.protectedTags.remove tag := by
    simp only [GlobalState.endCall,FrameState.addProtector,Array.foldl_push,Array.foldl_empty]
  have uniqueHidden : ∀ index value, tree.nodeAt index = some value → value.tag = tag → value.isExposed = false := by
    intro index value found tagged
    have first := runtime.formed.allocator.nodeTags index value found
    have second := runtime.formed.allocator.nodeTags anchor node present
    rw [tagged,←sameTag,second] at first
    have equal : index = anchor := (Option.some.inj first).symm
    subst index
    have equalNode := Option.some.inj (found.symm.trans present)
    subst value
    exact hidden
  refine ⟨?_,?_,?_⟩
  · refine ⟨⟨runtime.formed.toState,?_⟩,?_,runtime.possible,?_⟩
    · intro position valid
      rw [protectorEq]
      exact profile tree _ _ _ (GeneralBorrowRelease.remove_weakens global.protectedTags tag) (runtime.formed.profile position valid)
    · intro position valid
      rw [protectorEq]
      exact GeneralBorrowProtectorCacheMap.remove_hidden tree _ global.protectedTags tag (runtime.coherent position valid) uniqueHidden
    · refine ⟨runtime.below.mapping,?_⟩
      intro row member
      rw [protectorEq] at member
      exact runtime.below.protectors row (Array.mem_filter.mp member).1
  · rw [protectorEq]
    simp only [ProtectedTags.contains,ProtectedTags.get_remove_same,Option.isSome_none]
  · intro query different
    rw [protectorEq]
    exact GeneralBorrowProtectorCacheMap.remove_other global.protectedTags tag query different
/-- Actual helper release followed by its singleton owning-frame endCall.
No release outcome, final runtime or protector-frame equation is a premise. -/
theorem release_end_call (tree : BorrowTree) (global : GlobalState)
    (before : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (allocation : AllocId) (tag : BorTag) (anchor selected : UniIndex) (maximum : Option BorTag) (offset len : UInt64)
    (positive : GeneralBorrowReadRowRange.Positive tree global.protectedTags anchor selected maximum offset len)
    (node : TreeNode) (present : tree.nodeAt anchor = some node) (sameTag : node.tag = tag) (hidden : node.isExposed = false)
    (tagged : tree.indexOfTag tag = some anchor) (distinct : tree.roots.toList.Nodup)
    (order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] → GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (short : tree.nodes.size < 65536)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree anchor .Read offset (offset+len)) :
    let actual := tree.releaseProtector tag global.protectedTags
    let after := global.endCall (({} : FrameState).addProtector allocation tag)
    actual.status = .Released ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree after ∧
    after.protectedTags.contains tag = false ∧
    (∀ query, query ≠ tag → after.protectedTags.get query = global.protectedTags.get query) ∧
    actual.tree = {tree with locations := actual.tree.locations} ∧ actual.tree.locations.size = tree.locations.size := by
  obtain ⟨done,runtime,rows,activity,frame,capacity⟩ := GeneralBorrowReadProtectorRelease.release tree global before
    tag anchor selected maximum offset len positive node present hidden tagged distinct order short active
  have presentAfter : (tree.releaseProtector tag global.protectedTags).tree.nodeAt anchor = some node := by
    have nodes := congrArg BorrowTree.nodes frame
    change (tree.releaseProtector tag global.protectedTags).tree.nodes.get anchor = some node
    rw [nodes]
    exact present
  obtain ⟨runtimeAfter,absent,other⟩ := end_call _ global runtime allocation tag anchor node presentAfter sameTag hidden
  exact ⟨done,runtimeAfter,absent,other,frame,capacity⟩
end DuplicatePrefix.GeneralBorrowHiddenProtectorDropRuntime
