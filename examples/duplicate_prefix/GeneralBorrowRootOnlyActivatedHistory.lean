import duplicate_prefix.GeneralBorrowRootOnlyActivation
import duplicate_prefix.GeneralBorrowRootOnlyMixedGeneration
namespace DuplicatePrefix.GeneralBorrowRootOnlyActivatedHistory
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowRootOnlyExposureExact DuplicatePrefix.GeneralBorrowRootOnlyRangeCache
open DuplicatePrefix.GeneralBorrowRootOnlyMixedHistory (Invariant cacheFor transport expose)
open DuplicatePrefix.GeneralBorrowPartitionState DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowExposedProtectedHistory
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
def SupportedOrdinary {bytes : UInt64} : GeneralBorrowPartitionGcHistory.Action bytes → Prop
  | .collect .. => False
  | _ => True

def Supported {bytes : UInt64} : Action bytes → Prop
  | .ordinary (.ordinary request) => SupportedOrdinary request
  | .ordinary (.lifetime ..) => False
  | .exposeRoot => True

/-- Cache coherence for actual ordinary root accesses and Shared/Default
positive/zero stages. Collection is explicitly excluded here. -/
theorem ordinary (tree : BorrowTree) (root : UniIndex) (bytes : UInt64) (s : State tree root bytes)
    (action : GeneralBorrowPartitionGcHistory.Action bytes) (supported : SupportedOrdinary action)
    (initial : Invariant tree root)
    (fresh : ∀ tag ∈ action.tags, GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (room : tree.nodes.size+action.tags.length+4 ≤ 4294967295) :
    Invariant (GeneralBorrowPartitionGcHistory.next tree s.node.tag bytes action) root := by
  have known := initial.2 s.node s.star.present
  let cache := cacheFor root s.node.isExposed
  have combine : ∀ after, RootOnly after root ∧ Every (LocationInvariant cache root) after.locations ∧
      (after.nodes.get root).map TreeNode.isExposed = (tree.nodes.get root).map TreeNode.isExposed → Invariant after root := by
    intro after facts
    exact transport tree after root s.node s.star.present facts.1 facts.2.1 facts.2.2
  cases action with
  | access request =>
    exact combine _ (GeneralBorrowRootOnlyStageFrames.access tree root bytes s request.offset request.len request.kind request.bounds cache initial.1 known)
  | shared tag offset len nonzero bounds =>
    exact combine _ (GeneralBorrowRootOnlyStageFrames.shared tree root bytes s offset len nonzero bounds tag
      (fresh tag (by simp [GeneralBorrowPartitionGcHistory.Action.tags]))
      (by simpa [GeneralBorrowPartitionGcHistory.Action.tags,Nat.add_assoc] using room) cache initial.1 known)
  | reserved tag offset len nonzero bounds =>
    exact combine _ (GeneralBorrowRootOnlyStageFrames.reserve tree root bytes s offset len nonzero bounds tag
      (fresh tag (by simp [GeneralBorrowPartitionGcHistory.Action.tags]))
      (by simpa [GeneralBorrowPartitionGcHistory.Action.tags,Nat.add_assoc] using room) cache initial.1 known)
  | sharedZero tag offset bounds =>
    exact combine _ (GeneralBorrowRootOnlyStageFrames.zero_shared tree root bytes s offset bounds tag
      (fresh tag (by simp [GeneralBorrowPartitionGcHistory.Action.tags]))
      (by simpa [GeneralBorrowPartitionGcHistory.Action.tags,Nat.add_assoc] using room) cache initial.1 known)
  | reservedZero tag offset bounds =>
    exact combine _ (GeneralBorrowRootOnlyStageFrames.zero_reserve tree root bytes s offset bounds tag
      (fresh tag (by simp [GeneralBorrowPartitionGcHistory.Action.tags]))
      (by simpa [GeneralBorrowPartitionGcHistory.Action.tags,Nat.add_assoc] using room) cache initial.1 known)
  | activate tag offset len nonzero bounds =>
    exact combine _ (GeneralBorrowRootOnlyActivation.stage tree root bytes s offset len nonzero bounds tag
      (fresh tag (by simp [GeneralBorrowPartitionGcHistory.Action.tags]))
      (by simpa [GeneralBorrowPartitionGcHistory.Action.tags,Nat.add_assoc] using room) cache initial.1 known)
  | collect live => exact False.elim supported

/-- One supported actual public history action preserves the certificate. -/
theorem advance (tree : BorrowTree) (global : GlobalState) (root : UniIndex) (bytes : UInt64)
    (parentTag : BorTag) (s : State tree root bytes) (tagged : s.node.tag = parentTag)
    (action : Action bytes) (supported : Supported action) (initial : Invariant tree root)
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
    | lifetime tag offset len nonzero bounds allocation => exact False.elim supported
    | ordinary request =>
      have result := ordinary tree root bytes s request supported initial fresh room
      rw [tagged] at result
      exact result

/-- Any finite supported mixture of actual root exposure, root Read/Write and
Shared/Default positive/zero stages preserves genuine exact cache coherence.
This induction excludes GC and protected lifetimes explicitly. -/
theorem run (tree : BorrowTree) (global : GlobalState) (empty : global.protectedTags = {})
    (root : UniIndex) (bytes : UInt64) (parentTag : BorTag) (s : State tree root bytes)
    (tagged : s.node.tag = parentTag) (actions : List (Action bytes))
    (supported : ∀ action ∈ actions, Supported action) (initial : Invariant tree root)
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
    have invariant := advance tree global root bytes parentTag s tagged action (supported action (by simp)) initial
      (fun tag member => fresh tag (List.mem_append_left _ member)) (by rw [List.length_append] at room;omega)
    obtain ⟨⟨post,postTag⟩⟩ := first.2.2.1
    apply ih _ _ first.2.1 post postTag
      (fun later member => supported later (by simp [member])) invariant separate.2.1
    · intro tag member
      apply first.2.2.2.2 tag
      · intro earlier;exact separate.2.2 tag earlier tag member rfl
      · exact fresh tag (List.mem_append_right _ member)
    · have growth := first.2.2.2.1
      rw [List.length_append] at room
      omega

/-- Genuine cache coherence generated from allocation and the actual public
finite history. Root exposures, Read/Write, positive Shared/Default and real
zero-length constructors may be arbitrarily interleaved. GC and protected lifetimes remain excluded by Supported. There is no success, initial
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
  exact ⟨completed.1,GeneralBorrowRootOnlyActivatedHistory.run _ global empty GeneralBorrowFullSharedSeed.root capacity rootTag
    initial initialTag actions supported (GeneralBorrowRootOnlyMixedGeneration.seed capacity nonzero rootTag) unique fresh budget⟩

end DuplicatePrefix.GeneralBorrowRootOnlyActivatedHistory
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowRootOnlyActivatedHistory." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved root-only activated history dependency {dependency}"
