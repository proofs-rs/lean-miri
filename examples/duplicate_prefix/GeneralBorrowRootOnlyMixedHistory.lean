import duplicate_prefix.GeneralBorrowRootOnlyStageFrames
import duplicate_prefix.GeneralBorrowExposedProtectedGeneration
namespace DuplicatePrefix.GeneralBorrowRootOnlyMixedHistory
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowRootOnlyExposureExact DuplicatePrefix.GeneralBorrowRootOnlyRangeCache
open DuplicatePrefix.GeneralBorrowPartitionState DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowExposedProtectedHistory
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- The exact canonical cache before/after the first original-root exposure. -/
def cacheFor (root : UniIndex) (exposed : Bool) : ExposedCache :=
  if exposed then GeneralBorrowUniqueRootExposure.bump {} root else {}

/-- A concrete root-only protocol certificate. Its cache is derived from the
present original root's real exposure flag, not from an independent phase. -/
def Invariant (tree : BorrowTree) (root : UniIndex) : Prop :=
  RootOnly tree root ∧ ∀ node, tree.nodes.get root = some node →
    Every (LocationInvariant (cacheFor root node.isExposed) root) tree.locations

def SupportedOrdinary {bytes : UInt64} : GeneralBorrowPartitionGcHistory.Action bytes → Prop
  | .activate .. | .collect .. => False
  | _ => True

def Supported {bytes : UInt64} : Action bytes → Prop
  | .ordinary (.ordinary request) => SupportedOrdinary request
  | .ordinary (.lifetime ..) => False
  | .exposeRoot => True

/-- Transport exact source frames while retaining the real root exposure flag. -/
theorem transport (tree after : BorrowTree) (root : UniIndex) (node : TreeNode)
    (present : tree.nodes.get root = some node)
    (only : RootOnly after root)
    (cache : Every (LocationInvariant (cacheFor root node.isExposed) root) after.locations)
    (flag : (after.nodes.get root).map TreeNode.isExposed = (tree.nodes.get root).map TreeNode.isExposed) :
    Invariant after root := by
  refine ⟨only,?_⟩
  intro later found
  have equal : later.isExposed = node.isExposed := Option.some.inj (by simpa only [found,present,Option.map_some] using flag)
  rw [equal]
  exact cache

/-- Cache coherence for actual ordinary root accesses and Shared/Default
positive/zero stages. Activation and collection are explicitly excluded here. -/
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
  | activate tag offset len nonzero bounds => exact False.elim supported
  | collect live => exact False.elim supported

/-- Actual root exposure is coherent on every partition; repeated exposures
are source early returns and require no counter or history-length budget. -/
theorem expose (tree : BorrowTree) (root : UniIndex) (bytes : UInt64) (s : State tree root bytes)
    (initial : Invariant tree root) : Invariant (tree.exposeTag {} s.node.tag).tree root := by
  have tagged := s.allocator.nodeTags root s.node s.star.present
  cases flag : s.node.isExposed with
  | true =>
    rw [GeneralBorrowRootExposureFrame.already tree s.node.tag root s.node tagged s.star.present flag {}]
    exact initial
  | false =>
    have known := initial.2 s.node s.star.present
    simp only [cacheFor,flag,Bool.false_eq_true,ite_false] at known
    have updated := GeneralBorrowRootOnlyPartitionExposure.expose tree s.node.tag root s.node {} {} tagged s.star.present s.star.parentless flag known
    have frame := GeneralBorrowRootExposureFrame.expose tree s.node.tag root s.node tagged s.star.present
      (GeneralBorrowStarCertificates.depth tree root s.node s.star) flag {}
    refine ⟨(expose_root_only tree s.node.tag root s.node tagged s.star.present
      (GeneralBorrowStarCertificates.depth tree root s.node s.star) initial.1 {}).2,?_⟩
    intro node present
    rw [frame.2.2,GeneralBorrowFreshLocation.get_same] at present
    cases present
    exact updated.2

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
This induction excludes activation, GC and protected lifetimes explicitly. -/
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

end DuplicatePrefix.GeneralBorrowRootOnlyMixedHistory
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowRootOnlyMixedHistory." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved root-only mixed-history dependency {dependency}"
