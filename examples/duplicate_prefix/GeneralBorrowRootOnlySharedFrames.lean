import duplicate_prefix.GeneralBorrowRootOnlyConstructorFrames

namespace DuplicatePrefix.GeneralBorrowRootOnlySharedFrames
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowRootOnlyExposureExact DuplicatePrefix.GeneralBorrowRootOnlyRangeCache
open DuplicatePrefix.GeneralBorrowSifa DuplicatePrefix.GeneralBorrowRootOnlyConstructorFrames DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- Replacing the original root's metadata cannot expose any child. -/
theorem insert_root (tree : BorrowTree) (root : UniIndex) (node : TreeNode) (only : RootOnly tree root) :
    RootOnly {tree with nodes := tree.nodes.insert root node} root := by
  intro index found present exposed
  by_cases same : index = root
  · exact same
  · rw [GeneralBorrowFreshLocation.get_other _ _ _ _ same] at present
    exact only index found present exposed

/-- The actual graph attachment has one unexposed new child and changes only
the original root's child array. Append/reuse is deliberately immaterial here. -/
theorem attach (tree : BorrowTree) (root child : UniIndex) (rootNode childNode : TreeNode)
    (only : RootOnly tree root) (unexposed : childNode.isExposed = false) :
    RootOnly (GeneralBorrowFreshGraph.attached tree child root rootNode childNode) root := by
  exact insert_root {tree with nodes := tree.nodes.insert child childNode} root _
    (insert_unexposed_root_only tree root child childNode only unexposed)

/-- The real positive shared append constructor preserves root-only exposure,
Unique root storage and the exact per-location cache, after its actual SIFA scan. -/
theorem append (input : GeneralBorrowFreshMetadataChildShared.Input) (cache : ExposedCache)
    (only : RootOnly input.tree input.parent)
    (initial : Every (LocationInvariant cache input.parent) input.tree.locations) :
    RootOnly (GeneralBorrowFreshMetadataChildShared.result input) input.parent ∧
    Every (LocationInvariant cache input.parent) (GeneralBorrowFreshMetadataChildShared.result input).locations := by
  have different := GeneralBorrowFreshNode.parent_not_fresh input.tree.nodes
    (GeneralBorrowFreshMetadataChildShared.index input) input.parent input.parentNode
    (GeneralBorrowFreshMetadataChildShared.at_end input) input.parentPresent
  have stageOnly : RootOnly (GeneralBorrowFreshMetadataChildShared.stage input) input.parent := by
    simpa only [RootOnly,GeneralBorrowFreshMetadataChildShared.stage,GeneralBorrowFreshMetadataChildAttach.staged]
      using attach input.tree input.parent (GeneralBorrowFreshMetadataChildShared.index input) input.parentNode
        (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent) only rfl
  have installed : Every (LocationInvariant cache input.parent) (GeneralBorrowFreshMetadataChildShared.stage input).locations := by
    simpa only [GeneralBorrowFreshMetadataChildShared.stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshMetadataChildShared.locations]
      using materialize input.tree.locations input.parent (GeneralBorrowFreshMetadataChildShared.index input) different cache
      GeneralBorrowFreshAnchor.sharedState (Size.ofBytes input.offset) (Size.ofBytes input.len) input.well input.bounds initial
  let P := fun tree : BorrowTree => RootOnly tree input.parent ∧ Every (LocationInvariant cache input.parent) tree.locations
  have result : P (sourceUpdateSifa (GeneralBorrowFreshMetadataChildShared.stage input) input.parent .Read).1 :=
    sifa (GeneralBorrowFreshMetadataChildShared.stage input) input.parent input.parent .Read cache stageOnly installed
  exact (congrArg P (GeneralBorrowFreshMetadataChildShared.tree_eq input)).mpr result

/-- The real positive shared reused-slot constructor has the same exact frame;
the slot is selected by its actual allocator certificate. -/
theorem reuse (input : GeneralBorrowFreshMetadataChildSharedReuse.Input) (cache : ExposedCache)
    (only : RootOnly input.tree input.parent)
    (initial : Every (LocationInvariant cache input.parent) input.tree.locations) :
    RootOnly (GeneralBorrowFreshMetadataChildSharedReuse.result input) input.parent ∧
    Every (LocationInvariant cache input.parent) (GeneralBorrowFreshMetadataChildSharedReuse.result input).locations := by
  have different := GeneralBorrowFreshReuseNode.parent_not_vacant input.tree.nodes
    input.index input.parent input.parentNode input.vacant input.parentPresent
  have stageOnly : RootOnly (GeneralBorrowFreshMetadataChildSharedReuse.stage input) input.parent := by
    simpa only [RootOnly,GeneralBorrowFreshMetadataChildSharedReuse.index,GeneralBorrowFreshMetadataChildSharedReuse.stage,GeneralBorrowFreshMetadataChildAttach.staged]
      using attach input.tree input.parent input.index input.parentNode
        (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent) only rfl
  have installed : Every (LocationInvariant cache input.parent) (GeneralBorrowFreshMetadataChildSharedReuse.stage input).locations := by
    simpa only [GeneralBorrowFreshMetadataChildSharedReuse.index,GeneralBorrowFreshMetadataChildSharedReuse.stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshMetadataChildSharedReuse.locations]
      using materialize input.tree.locations input.parent input.index different cache
      GeneralBorrowFreshAnchor.sharedState (Size.ofBytes input.offset) (Size.ofBytes input.len) input.well input.bounds initial
  let P := fun tree : BorrowTree => RootOnly tree input.parent ∧ Every (LocationInvariant cache input.parent) tree.locations
  have result : P (sourceUpdateSifa (GeneralBorrowFreshMetadataChildSharedReuse.stage input) input.parent .Read).1 :=
    sifa (GeneralBorrowFreshMetadataChildSharedReuse.stage input) input.parent input.parent .Read cache stageOnly installed
  exact (congrArg P (GeneralBorrowFreshMetadataChildSharedReuse.tree_eq input)).mpr result

end DuplicatePrefix.GeneralBorrowRootOnlySharedFrames
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowRootOnlySharedFrames." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved root-only shared frame dependency {dependency}"
