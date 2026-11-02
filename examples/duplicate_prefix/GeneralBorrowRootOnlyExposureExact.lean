import duplicate_prefix.GeneralBorrowUniqueRootExposure
import duplicate_prefix.GeneralBorrowRootExposureSeed

namespace DuplicatePrefix.GeneralBorrowRootOnlyExposureExact
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowUniqueRootExposure
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Every currently present exposed node is the original concrete root.
This predicate deliberately says nothing about permission or cache coherence. -/
def RootOnly (tree : BorrowTree) (root : UniIndex) : Prop :=
  ∀ index node, tree.nodes.get index = some node → node.isExposed = true → index = root

/-- Marking the original root cannot expose a child, including a reused slot. -/
theorem mark_root_only (tree : BorrowTree) (root : UniIndex) (node : TreeNode)
    (only : RootOnly tree root) :
    RootOnly {tree with nodes := tree.nodes.insert root {node with isExposed := true}} root := by
  intro index found present exposed
  by_cases same : index = root
  · exact same
  · rw [GeneralBorrowFreshLocation.get_other _ _ _ _ same] at present
    exact only index found present exposed

/-- The real exposure operation preserves root-only exposure for any bounded
acyclic graph. No cache-validity or operation-success hypothesis is required. -/
theorem expose_root_only (tree : BorrowTree) (tag : BorTag) (root : UniIndex) (node : TreeNode)
    (tagged : tree.indexOfTag tag = some root) (present : tree.nodeAt root = some node)
    (depth : DuplicatePrefix.GeneralBorrowExposure.ParentDepth tree.nodes)
    (only : RootOnly tree root) (protections : ProtectedTags) :
    (tree.exposeTag protections tag).outcome = .ok () ∧
    RootOnly (tree.exposeTag protections tag).tree root := by
  cases flag : node.isExposed with
  | false =>
    have facts := GeneralBorrowRootExposureFrame.expose tree tag root node tagged present depth flag protections
    refine ⟨facts.1,?_⟩
    intro index found stored exposed
    rw [facts.2.2] at stored
    exact mark_root_only tree root node only index found stored exposed
  | true =>
    rw [GeneralBorrowRootExposureFrame.already tree tag root node tagged present flag protections]
    exact ⟨rfl,only⟩

/-- The exact source update at a parentless root. It works independently at
any partition location: the Unique permission selects Write even when protected.
The operation changes no counter at any other node. -/
theorem unique_location_update (cache : ExposedCache) (nodes : UniValMap TreeNode)
    (root : UniIndex) (node : TreeNode) (state : LocationState) (held : Bool)
    (present : nodes.get root = some node) (parentless : node.parent = none)
    (unique : state.permission = .Unique) :
    cache.updateExposure nodes root .None (state.permission.strongestAllowedLocalAccess held) =
      ⟨bump cache root,.ok ()⟩ := by
  rw [unique]
  exact root_cache cache nodes root node present parentless

/-- Fresh root-only exposure contributes exactly one read and one write, with
no history-length assumption and no UInt16 wraparound. -/
theorem fresh_counters (root query : UniIndex) :
    ((bump {} root).nodes.get query).getD {} =
      if query = root then (⟨1,1⟩ : ExposedCacheNode) else {} := by
  by_cases same : query = root
  · subst query
    simp only [bump,GeneralBorrowFreshLocation.get_same,Option.getD_some,↓reduceIte]
    rfl
  · simp only [bump,GeneralBorrowFreshLocation.get_other _ _ _ _ same,ite_eq_right same]
    rfl

/-- Repeated real exposure requests, with arbitrary per-request protector maps. -/
def exposeMany (tree : BorrowTree) (tag : BorTag) : List ProtectedTags → BorrowTree
  | [] => tree
  | protections :: rest => exposeMany (tree.exposeTag protections tag).tree tag rest

/-- Any finite number of repeated exposures is the actual early-return path;
there is no numerical length budget. -/
theorem exposeMany_already (tree : BorrowTree) (tag : BorTag) (root : UniIndex) (node : TreeNode)
    (tagged : tree.indexOfTag tag = some root) (present : tree.nodeAt root = some node)
    (exposed : node.isExposed = true) (requests : List ProtectedTags) :
    exposeMany tree tag requests = tree := by
  induction requests with
  | nil => rfl
  | cons protections rest ih =>
    simp only [exposeMany,GeneralBorrowRootExposureFrame.already tree tag root node tagged present exposed protections]
    exact ih

/-- Starting from real allocation, a first real exposure followed by any finite
number of re-exposures has the exact generated one-read/one-write cache.
No success or cache premise and no history-length bound is supplied. -/
theorem allocated_repeated (capacity : UInt64) (nonzero : capacity ≠ 0) (tag : BorTag)
    (first : ProtectedTags) (rest : List ProtectedTags) :
    exposeMany (BorrowTree.new tag (Size.ofBytes capacity)) tag (first :: rest) =
      GeneralBorrowRootExposureSeed.exposedTree capacity tag := by
  rw [exposeMany,GeneralBorrowRootExposureSeed.expose capacity nonzero tag first]
  apply exposeMany_already _ tag GeneralBorrowRootExposureSeed.root (GeneralBorrowRootExposureSeed.rootNode tag true)
  · simp [GeneralBorrowRootExposureSeed.exposedTree,BorrowTree.indexOfTag,UniKeyMap.get]
  · rfl
  · rfl

/-- Adding a genuinely unexposed child cannot introduce an exposed child.
This frame applies equally to append and allocator slot reuse. -/
theorem insert_unexposed_root_only (tree : BorrowTree) (root child : UniIndex) (node : TreeNode)
    (only : RootOnly tree root) (unexposed : node.isExposed = false) :
    RootOnly {tree with nodes := tree.nodes.insert child node} root := by
  intro index found present exposed
  by_cases same : index = child
  · subst index
    rw [GeneralBorrowFreshLocation.get_same] at present
    have equal := Option.some.inj present
    subst found
    rw [unexposed] at exposed
    cases exposed
  · rw [GeneralBorrowFreshLocation.get_other _ _ _ _ same] at present
    exact only index found present exposed

/-- Actual protector release for any present unexposed node is an exact frame:
no range scan or cache update runs, irrespective of partition or cache contents. -/
theorem release_unexposed (tree : BorrowTree) (tag : BorTag) (index : UniIndex) (node : TreeNode)
    (tagged : tree.indexOfTag tag = some index) (present : tree.nodeAt index = some node)
    (unexposed : node.isExposed = false) :
    tree.updateExposureForProtectorRelease tag = ⟨tree,.ok ()⟩ := by
  simp only [BorrowTree.updateExposureForProtectorRelease,tagged,present,unexposed,
    Bool.not_false,↓reduceIte,Id.run,pure]

/-- In a root-only protocol the release of every actual child is an exact
cache frame, including the protected mutable child of a closed lifetime. -/
theorem release_child (tree : BorrowTree) (root child : UniIndex) (tag : BorTag) (node : TreeNode)
    (only : RootOnly tree root) (different : child ≠ root)
    (tagged : tree.indexOfTag tag = some child) (present : tree.nodeAt child = some node) :
    tree.updateExposureForProtectorRelease tag = ⟨tree,.ok ()⟩ := by
  apply release_unexposed tree tag child node tagged present
  cases flag : node.isExposed with
  | false => rfl
  | true => exact False.elim (different (only child node present flag))

/-- Unique ownership gives the same root exposure level on both sides of
protector release; the real cache update early-returns with the original cache. -/
theorem unique_release_cache (cache : ExposedCache) (nodes : UniValMap TreeNode)
    (root : UniIndex) (state : LocationState) (unique : state.permission = .Unique) :
    cache.updateExposure nodes root (state.permission.strongestAllowedLocalAccess true)
      (state.permission.strongestAllowedLocalAccess false) = ⟨cache,.ok ()⟩ := by
  rw [unique]
  rfl

end DuplicatePrefix.GeneralBorrowRootOnlyExposureExact

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowRootOnlyExposureExact." then
      for dependency in (←collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved root-only exposure dependency {dependency}"
