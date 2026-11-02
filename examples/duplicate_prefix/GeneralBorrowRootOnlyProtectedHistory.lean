import duplicate_prefix.GeneralBorrowRootOnlyGcHistory
import duplicate_prefix.GeneralBorrowRootOnlyProtectedLifetime
import duplicate_prefix.GeneralBorrowRootOnlyMixedGeneration
namespace DuplicatePrefix.GeneralBorrowRootOnlyProtectedHistory
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowRootOnlyExposureExact DuplicatePrefix.GeneralBorrowRootOnlyRangeCache
open DuplicatePrefix.GeneralBorrowRootOnlyMixedHistory (Invariant cacheFor transport expose)
open DuplicatePrefix.GeneralBorrowPartitionState DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowExposedProtectedHistory
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
/-- Every actual public history action preserves the root-only cache certificate. -/
theorem advance (tree : BorrowTree) (global : GlobalState) (empty : global.protectedTags = {}) (root : UniIndex) (bytes : UInt64)
    (parentTag : BorTag) (s : State tree root bytes) (tagged : s.node.tag = parentTag)
    (fixed : root = GeneralBorrowFullSharedSeed.root) (action : Action bytes) (initial : Invariant tree root)
    (fresh : ∀ tag ∈ action.tags, GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (room : tree.nodes.size+action.tags.length+4 ≤ 4294967295) :
    Invariant (nextTree tree global parentTag bytes action) root := by
  cases action with
  | exposeRoot =>
    have result := expose tree root bytes s initial
    rw [tagged] at result
    exact result
  | ordinary request =>
    cases request with
    | lifetime tag offset len nonzero bounds allocation =>
      have cache := initial.2 s.node s.star.present
      have frame := GeneralBorrowRootOnlyProtectedLifetime.stage tree root bytes s offset len nonzero bounds tag
        (fresh tag (by simp [Action.tags,GeneralBorrowProtectedMutableHistory.Action.tags]))
        (by simpa [Action.tags,GeneralBorrowProtectedMutableHistory.Action.tags,Nat.add_assoc] using room)
        global empty allocation (cacheFor root s.node.isExposed) initial.1 cache
      have result := transport tree _ root s.node s.star.present frame.1 frame.2.1 frame.2.2
      rw [tagged] at result
      exact result
    | ordinary request =>
      have result := GeneralBorrowRootOnlyGcHistory.ordinary tree root bytes s fixed request True.intro initial fresh room
      rw [tagged] at result
      exact result

/-- Any finite mixture of actual root exposure, root Read/Write and
Shared/Default positive/zero stages preserves genuine exact cache coherence.
Closed Strong-protected mutable lifetimes are included with actual global-state threading. -/
theorem run (tree : BorrowTree) (global : GlobalState) (empty : global.protectedTags = {})
    (root : UniIndex) (bytes : UInt64) (parentTag : BorTag) (s : State tree root bytes)
    (tagged : s.node.tag = parentTag) (fixed : root = GeneralBorrowFullSharedSeed.root) (actions : List (Action bytes))
    (initial : Invariant tree root)
    (unique : (actions.flatMap Action.tags).Nodup)
    (fresh : ∀ tag ∈ actions.flatMap Action.tags, GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (room : tree.nodes.size+(actions.flatMap Action.tags).length+4 ≤ 4294967295) :
    Invariant (execute tree global parentTag bytes actions).1 root := by
  induction actions generalizing tree global with
  | nil => exact initial
  | cons action rest ih =>
    have tags : ((action :: rest).flatMap Action.tags) = action.tags ++ rest.flatMap Action.tags := rfl
    rw [tags] at unique fresh room
    have separate := List.nodup_append.mp unique
    have first := GeneralBorrowExposedProtectedHistory.advance tree global empty root bytes parentTag s tagged action
      (fun tag member => fresh tag (List.mem_append_left _ member)) (by rw [List.length_append] at room;omega)
    have invariant := advance tree global empty root bytes parentTag s tagged fixed action initial
      (fun tag member => fresh tag (List.mem_append_left _ member)) (by rw [List.length_append] at room;omega)
    obtain ⟨⟨post,postTag⟩⟩ := first.2.2.1
    apply ih _ _ first.2.1 post postTag
      invariant separate.2.1
    · intro tag member
      apply first.2.2.2.2 tag
      · intro earlier;exact separate.2.2 tag earlier tag member rfl
      · exact fresh tag (List.mem_append_right _ member)
    · have growth := first.2.2.2.1
      rw [List.length_append] at room
      omega

/-- Genuine cache coherence generated from allocation and the actual public
finite history. Root exposures, Read/Write, positive Shared/Default and real
zero-length constructors may be arbitrarily interleaved. Closed Strong-protected mutable lifetimes, actual activation and full GC are included. There is no success, initial
cache, intermediate-state or history-length premise. -/
theorem generated (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag tag : BorTag)
    (different : rootTag ≠ tag) (global : GlobalState) (empty : global.protectedTags = {})
    (actions : List (Action capacity))
    (unique : (actions.flatMap Action.tags).Nodup) (rootUnused : rootTag ∉ actions.flatMap Action.tags)
    (room : 1+(actions.flatMap Action.tags).length+4 ≤ 4294967295) :
    let initial := BorrowTree.new rootTag (Size.ofBytes capacity)
    AllCompleted initial global rootTag capacity actions ∧
    Invariant (execute initial global rootTag capacity actions).1 GeneralBorrowFullSharedSeed.root ∧
    Nonempty {post : State (execute initial global rootTag capacity actions).1 GeneralBorrowFullSharedSeed.root capacity //
      post.node.tag = rootTag} := by
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
  exact ⟨completed.1,GeneralBorrowRootOnlyProtectedHistory.run _ global empty GeneralBorrowFullSharedSeed.root capacity rootTag
    initial initialTag rfl actions (GeneralBorrowRootOnlyMixedGeneration.seed capacity nonzero rootTag) unique fresh budget,
    completed.2.2.1⟩

/-- Direct numerical coherence for the entire generated concrete protocol.
All present exposed nodes are the original root, that root is effectively
Unique at every partition location, and the real counters are exactly one
Read/Write there after exposure and zero elsewhere. The genuine operation
completion is included; no cache certificate or operation success is a premise. -/
theorem generated_counters (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag tag : BorTag)
    (different : rootTag ≠ tag) (global : GlobalState) (empty : global.protectedTags = {})
    (actions : List (Action capacity))
    (unique : (actions.flatMap Action.tags).Nodup) (rootUnused : rootTag ∉ actions.flatMap Action.tags)
    (room : 1+(actions.flatMap Action.tags).length+4 ≤ 4294967295) :
    let initial := BorrowTree.new rootTag (Size.ofBytes capacity)
    let final := (execute initial global rootTag capacity actions).1
    AllCompleted initial global rootTag capacity actions ∧
    ∃ node, final.nodes.get GeneralBorrowFullSharedSeed.root = some node ∧
      RootOnly final GeneralBorrowFullSharedSeed.root ∧
      Every (fun location : LocationTree => StoredUnique location GeneralBorrowFullSharedSeed.root ∧
        ∀ query, (location.exposedCache.nodes.get query).getD {} =
          if node.isExposed ∧ query = GeneralBorrowFullSharedSeed.root then (⟨1,1⟩ : ExposedCacheNode) else {}) final.locations := by
  dsimp only
  have facts := generated capacity nonzero rootTag tag different global empty actions unique rootUnused room
  obtain ⟨⟨post,postTag⟩⟩ := facts.2.2
  refine ⟨facts.1,post.node,post.star.present,facts.2.1.1,?_⟩
  intro position valid
  refine ⟨(facts.2.1.2 post.node post.star.present position valid).1,?_⟩
  intro query
  exact GeneralBorrowRootOnlyMixedGeneration.counters _ GeneralBorrowFullSharedSeed.root post.node facts.2.1
    post.star.present position valid query

end DuplicatePrefix.GeneralBorrowRootOnlyProtectedHistory
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowRootOnlyProtectedHistory." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved root-only protected history dependency {dependency}"
