import duplicate_prefix.GeneralBorrowRootOnlyMixedHistory
namespace DuplicatePrefix.GeneralBorrowRootOnlyMixedGeneration
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowRootOnlyMixedHistory DuplicatePrefix.GeneralBorrowRootOnlyRangeCache
open DuplicatePrefix.GeneralBorrowExposedProtectedHistory DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- Real allocation supplies the full initial exact-cache certificate. -/
theorem seed (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag : BorTag) :
    Invariant (BorrowTree.new rootTag (Size.ofBytes capacity)) GeneralBorrowFullSharedSeed.root := by
  have original := GeneralBorrowFullSharedSeed.tree_eq capacity nonzero rootTag
  change GeneralBorrowFullSharedSeed.tree capacity nonzero rootTag = _ at original
  refine ⟨?_,?_⟩
  · intro index node present exposed
    have valid := GeneralBorrowNodeUpdate.lookup_valid (BorrowTree.new rootTag (Size.ofBytes capacity)).nodes index node present
    change index.toNat < (GeneralBorrowFullSharedSeed.tree capacity nonzero rootTag).nodes.data.size at valid
    rw [original] at valid
    change index.toNat < 1 at valid
    apply GeneralBorrowNodeUpdate.index_injective index GeneralBorrowFullSharedSeed.root
    change index.toNat = 0
    omega
  · intro node present
    have rootPresent : (BorrowTree.new rootTag (Size.ofBytes capacity)).nodes.get GeneralBorrowFullSharedSeed.root =
        some (GeneralBorrowFullSharedSeed.node rootTag) := by
      change (GeneralBorrowFullSharedSeed.tree capacity nonzero rootTag).nodes.get _ = _
      rw [original]
      rfl
    have equal : node = GeneralBorrowFullSharedSeed.node rootTag := Option.some.inj (present.symm.trans rootPresent)
    subst node
    change Every (LocationInvariant {} GeneralBorrowFullSharedSeed.root)
      (GeneralBorrowFullSharedSeed.tree capacity nonzero rootTag).locations
    rw [original]
    intro position valid
    change position < 1 at valid
    have zero : position = 0 := by omega
    subst position
    exact ⟨⟨GeneralBorrowWildcardLeaf.unique,rfl,rfl⟩,rfl⟩

/-- Genuine cache coherence generated from allocation and the actual public
finite history. Root exposures, Read/Write, positive Shared/Default and real
zero-length constructors may be arbitrarily interleaved. Activation, GC and
protected lifetimes remain excluded by Supported. There is no success, initial
cache, intermediate-state or history-length premise. -/
theorem generated (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag tag : BorTag)
    (different : rootTag ≠ tag) (global : GlobalState) (empty : global.protectedTags = {})
    (actions : List (Action capacity)) (supported : ∀ action ∈ actions, Supported action)
    (unique : (actions.flatMap Action.tags).Nodup) (rootUnused : rootTag ∉ actions.flatMap Action.tags)
    (room : 1+(actions.flatMap Action.tags).length+4 ≤ 4294967295) :
    let initial := BorrowTree.new rootTag (Size.ofBytes capacity)
    AllCompleted initial global rootTag capacity actions ∧
    Invariant (execute initial global rootTag capacity actions).1 GeneralBorrowFullSharedSeed.root := by
  dsimp only
  let initial := GeneralBorrowPartitionState.of_reusable _ GeneralBorrowFullSharedSeed.root capacity
    (GeneralBorrowReusableGeneration.seed capacity nonzero rootTag tag different)
  have initialTag : initial.node.tag = rootTag := rfl
  have fresh : ∀ nextTag ∈ actions.flatMap Action.tags,
      GeneralBorrowTagMap.Fresh (BorrowTree.new rootTag (Size.ofBytes capacity)).tagMapping nextTag := by
    intro nextTag member
    exact GeneralBorrowReusableGeneration.seed_fresh capacity nonzero rootTag nextTag (fun same => rootUnused (same ▸ member))
  have budget : (BorrowTree.new rootTag (Size.ofBytes capacity)).nodes.size+(actions.flatMap Action.tags).length+4 ≤ 4294967295 := by
    change (GeneralBorrowFullSharedSeed.tree capacity nonzero rootTag).nodes.size+_+4 ≤ _
    rw [GeneralBorrowFullSharedSeed.tree_eq]
    exact room
  have completed := GeneralBorrowExposedProtectedHistory.run _ global empty GeneralBorrowFullSharedSeed.root capacity rootTag
    initial initialTag actions unique fresh budget
  exact ⟨completed.1,GeneralBorrowRootOnlyMixedHistory.run _ global empty GeneralBorrowFullSharedSeed.root capacity rootTag
    initial initialTag actions supported (seed capacity nonzero rootTag) unique fresh budget⟩

/-- At every location the actual counter values are exactly one Read/Write at
the exposed original root and zero everywhere else. No finite-history counter
budget is needed: each counter is at most one. -/
theorem counters (tree : BorrowTree) (root : UniIndex) (node : TreeNode)
    (initial : Invariant tree root) (present : tree.nodes.get root = some node)
    (position : Nat) (valid : position < tree.locations.entries.size) (query : UniIndex) :
    ((tree.locations.entries[position].data.exposedCache.nodes.get query).getD {}) =
      if node.isExposed ∧ query = root then (⟨1,1⟩ : ExposedCacheNode) else {} := by
  have cache := (initial.2 node present position valid).2
  rw [cache]
  cases exposed : node.isExposed with
  | false => simp only [cacheFor,Bool.false_eq_true,ite_false,false_and];rfl
  | true =>
    simp only [cacheFor,ite_true,true_and]
    exact GeneralBorrowRootOnlyExposureExact.fresh_counters root query

end DuplicatePrefix.GeneralBorrowRootOnlyMixedGeneration
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowRootOnlyMixedGeneration." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved root-only mixed generation dependency {dependency}"
