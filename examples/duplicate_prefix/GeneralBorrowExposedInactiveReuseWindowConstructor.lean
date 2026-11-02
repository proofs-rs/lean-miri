import duplicate_prefix.GeneralBorrowExposedInactiveWindowConstructor
import duplicate_prefix.GeneralBorrowFreshMetadataChildSharedReuse
import duplicate_prefix.GeneralBorrowFreshMetadataChildDefaultReuse
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutableReuse
import duplicate_prefix.GeneralBorrowFreshStagePool

namespace DuplicatePrefix.GeneralBorrowExposedInactiveReuseWindowConstructor
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowView GeneralBorrowExposedConstructorAncestry GeneralBorrowFreshMetadataChildAttach
open GeneralBorrowExposedInactiveConstructor GeneralBorrowExposedInactiveWindowConstructor GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- A coherent nonempty free pool is incompatible with the dense alignment
required by the current append-only Input, even though actual reuse is valid.
This is a restriction of that proof interface, not an unsafe-execution claim. -/
theorem pool_not_dense (tree : BorrowTree) (accounting : GeneralBorrowFreshStagePool.Accounting tree)
    (index : UniIndex) (available : tree.tagMapping.deassigned.back? = some index) :
    tree.tagMapping.mapping.size < tree.nodes.data.size := by
  obtain ⟨rest, pool⟩ := Array.back?_eq_some_iff.mp available
  have positive : 0 < tree.tagMapping.deassigned.size := by rw [pool, Array.size_push]; omega
  unfold GeneralBorrowFreshStagePool.Accounting at accounting
  change tree.tagMapping.mapping.size + tree.tagMapping.deassigned.size = tree.nodes.data.size at accounting
  omega

/-- Recover every old exposed node and its default permission through an
actual vacant-slot attachment plus SIFA shape transport. No at-end index or
empty free pool is required. -/
theorem old_exposed (tree after : BorrowTree) (index parent query : UniIndex)
    (parentNode newNode node : TreeNode) (mapping : UniKeyMap BorTag)
    (locations : DedupRangeMap LocationTree) (vacant : tree.nodes.get index = none)
    (parentPresent : tree.nodeAt parent = some parentNode)
    (same : treeShape after = treeShape (staged tree index parent parentNode newNode mapping locations))
    (flags : GeneralBorrowFreshMetadataChildSifa.exposureShape after =
      GeneralBorrowFreshMetadataChildSifa.exposureShape (staged tree index parent parentNode newNode mapping locations))
    (different : query ≠ index) (present : after.nodeAt query = some node) (exposed : node.isExposed = true) :
    ∃ old, tree.nodeAt query = some old ∧ old.isExposed = true ∧
      node.defaultInitialPermission = old.defaultInitialPermission := by
  let before := staged tree index parent parentNode newNode mapping locations
  obtain ⟨oldStage, stored, tag, parentEq, children, permission⟩ :=
    GeneralBorrowFreshMetadata.node_fields after before same.symm query node present
  have exposure := GeneralBorrowFreshMetadataChildSifa.lookup_exposure before after flags query
  have presentNodes : after.nodes.get query = some node := present
  rw [presentNodes, stored] at exposure
  have stageExposed : oldStage.isExposed = true := by
    simpa only [Option.map_some, Option.some.injEq, exposed] using exposure.symm
  by_cases isParent : query = parent
  · subst query
    have parentStored : before.nodeAt parent = some (GeneralBorrowFreshGraph.updatedParent parentNode index) := by
      exact GeneralBorrowFreshMetadataChildReuseGraph.parent_lookup tree index parent parentNode newNode vacant parentPresent
    have equal : oldStage = GeneralBorrowFreshGraph.updatedParent parentNode index :=
      Option.some.inj (stored.symm.trans parentStored)
    subst oldStage
    exact ⟨parentNode, parentPresent, stageExposed, permission.symm⟩
  · have oldStored : tree.nodeAt query = some oldStage := by
      change (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode).nodeAt query = some oldStage at stored
      rw [GeneralBorrowFreshMetadataChildReuseGraph.other_lookup tree index parent query parentNode newNode vacant parentPresent isParent different] at stored
      exact stored
    exact ⟨oldStage, oldStored, stageExposed, permission.symm⟩

/-- A hidden reused leaf extends the selected anchor path exactly as append
would, but uses a real existing vacant table slot. -/
theorem reuse_location (tree after : BorrowTree) (index parent : UniIndex)
    (parentNode newNode : TreeNode) (mapping : UniKeyMap BorTag)
    (locations : DedupRangeMap LocationTree) (support : Nat → Prop) (location : LocationTree)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (same : treeShape after = treeShape (staged tree index parent parentNode newNode mapping locations))
    (flags : GeneralBorrowFreshMetadataChildSifa.exposureShape after =
      GeneralBorrowFreshMetadataChildSifa.exposureShape (staged tree index parent parentNode newNode mapping locations))
    (paths : GeneralBorrowFreshSharedPaths.Attach (topology tree) (topology after) parent.toNat index.toNat)
    (hidden : ∀ value, after.nodeAt index = some value → value.isExposed = false)
    (initial : Profile tree location parent support) :
    Profile after location index (extended support index) := by
  intro query node member present exposed
  have different : query ≠ index := by intro equal; subst query; rw [hidden node present] at exposed; cases exposed
  have natDifferent : query.toNat ≠ index.toNat := by
    intro equal; exact different (GeneralBorrowNodeUpdate.index_injective query index equal)
  have oldMember : support query.toNat := by
    rcases member with fresh | old
    · exact False.elim (natDifferent fresh)
    · exact old
  obtain ⟨old, found, oldExposed, permission⟩ := old_exposed tree after index parent query parentNode newNode node
    mapping locations vacant parentPresent same flags different present exposed
  rw [permission_same location location query old node rfl permission]
  have before := initial query old oldMember found oldExposed
  rw [paths.childPath]
  rcases before with active | inactive
  · exact .inl ⟨List.mem_cons_of_mem index.toNat active.1, active.2⟩
  · exact .inr ⟨by simpa only [List.mem_cons, not_or] using And.intro natDifferent inactive.1, inactive.2⟩

/-- The actual shared constructor consumes a vacant pool slot and preserves
only the requested window's exposed Profile, including real materialization
and allocation-wide SIFA. No operation success or outside-window Profile is
an input. Ownership/cache/complete call composition are separate obligations. -/
theorem shared (input : GeneralBorrowFreshMetadataChildSharedReuse.Input) (support : Nat → Prop) (lower upper : UInt64)
    (forest : GeneralBorrowForest.Forest (topology input.tree))
    (initial : OwnedOn (fun location => Profile input.tree location input.parent support) lower upper input.tree.locations) :
    OwnedOn (fun location => Profile (GeneralBorrowFreshMetadataChildSharedReuse.result input) location (GeneralBorrowFreshMetadataChildSharedReuse.index input)
      (extended support (GeneralBorrowFreshMetadataChildSharedReuse.index input))) lower upper (GeneralBorrowFreshMetadataChildSharedReuse.result input).locations := by
  let child := GeneralBorrowFreshMetadataChildSharedReuse.result input
  let index := GeneralBorrowFreshMetadataChildSharedReuse.index input
  let metadata := GeneralBorrowFreshMetadataChildSharedReuse.reuse input
  obtain ⟨node,present,_,_,_,_,notExposed⟩ := metadata.newNode
  have hidden : ∀ value, child.nodeAt index = some value → value.isExposed = false := by
    intro value found
    have equal := Option.some.inj (found.symm.trans present)
    exact equal ▸ notExposed
  have paths := GeneralBorrowFreshSharedPaths.of_reuse _ _ index.toNat input.parent.toNat
    (metadata.extension default default default) forest
  let predicate := fun location => Profile child location index (extended support index)
  have base : OwnedOn predicate lower upper input.tree.locations := by
    intro position valid positive beforeUpper afterLower
    exact reuse_location input.tree child index input.parent input.parentNode (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent)
      (GeneralBorrowFreshMetadataChildSharedReuse.mapping input) (GeneralBorrowFreshMetadataChildSharedReuse.locations input) support _ input.vacant input.parentPresent
      (GeneralBorrowFreshMetadataChildSharedReuse.shape input) (GeneralBorrowFreshMetadataChildSharedReuse.exposure input) paths hidden
      (initial position valid positive beforeUpper afterLower)
  have modified := modify_owned predicate lower upper input.tree.locations
    (Size.ofBytes input.offset) (Size.ofBytes input.len)
    (fun _ location => GeneralBorrowFreshMaterialization.materialized location index GeneralBorrowFreshAnchor.sharedState)
    input.well input.bounds base
    (fun _ location good => materialize child location index index GeneralBorrowFreshAnchor.sharedState _ hidden good)
  have rows := congrArg (fun shape => shape.2.2.1) (GeneralBorrowFreshMetadataChildSharedReuse.shape input)
  exact owned_shape child (GeneralBorrowFreshMetadataChildSharedReuse.stage input).locations child.locations index _ lower upper rows modified

/-- The actual default_child constructor consumes a vacant pool slot and preserves
only the requested window's exposed Profile, including real materialization
and allocation-wide SIFA. No operation success or outside-window Profile is
an input. Ownership/cache/complete call composition are separate obligations. -/
theorem default_child (input : GeneralBorrowFreshMetadataChildDefaultReuse.Input) (support : Nat → Prop) (lower upper : UInt64)
    (forest : GeneralBorrowForest.Forest (topology input.tree))
    (initial : OwnedOn (fun location => Profile input.tree location input.parent support) lower upper input.tree.locations) :
    OwnedOn (fun location => Profile (GeneralBorrowFreshMetadataChildDefaultReuse.result input) location (GeneralBorrowFreshMetadataChildDefaultReuse.index input)
      (extended support (GeneralBorrowFreshMetadataChildDefaultReuse.index input))) lower upper (GeneralBorrowFreshMetadataChildDefaultReuse.result input).locations := by
  let child := GeneralBorrowFreshMetadataChildDefaultReuse.result input
  let index := GeneralBorrowFreshMetadataChildDefaultReuse.index input
  let metadata := GeneralBorrowFreshMetadataChildDefaultReuse.reuse input
  obtain ⟨node,present,_,_,_,_,notExposed⟩ := metadata.newNode
  have hidden : ∀ value, child.nodeAt index = some value → value.isExposed = false := by
    intro value found
    have equal := Option.some.inj (found.symm.trans present)
    exact equal ▸ notExposed
  have paths := GeneralBorrowFreshSharedPaths.of_reuse _ _ index.toNat input.parent.toNat
    (metadata.extension default default default) forest
  let predicate := fun location => Profile child location index (extended support index)
  have base : OwnedOn predicate lower upper input.tree.locations := by
    intro position valid positive beforeUpper afterLower
    exact reuse_location input.tree child index input.parent input.parentNode (GeneralBorrowFreshDefaultChild.child input.newTag input.parent)
      (GeneralBorrowFreshMetadataChildDefaultReuse.mapping input) (GeneralBorrowFreshMetadataChildDefaultReuse.locations input) support _ input.vacant input.parentPresent
      (GeneralBorrowFreshMetadataChildDefaultReuse.shape input) (GeneralBorrowFreshMetadataChildDefaultReuse.exposure input) paths hidden
      (initial position valid positive beforeUpper afterLower)
  have modified := modify_owned predicate lower upper input.tree.locations
    (Size.ofBytes input.offset) (Size.ofBytes input.len)
    (fun _ location => GeneralBorrowFreshMaterialization.materialized location index GeneralBorrowFreshDefaultChild.inside)
    input.well input.bounds base
    (fun _ location good => materialize child location index index GeneralBorrowFreshDefaultChild.inside _ hidden good)
  have rows := congrArg (fun shape => shape.2.2.1) (GeneralBorrowFreshMetadataChildDefaultReuse.shape input)
  exact owned_shape child (GeneralBorrowFreshMetadataChildDefaultReuse.stage input).locations child.locations index _ lower upper rows modified

/-- The actual protected_mutable constructor consumes a vacant pool slot and preserves
only the requested window's exposed Profile, including real materialization
and allocation-wide SIFA. No operation success or outside-window Profile is
an input. Ownership/cache/complete call composition are separate obligations. -/
theorem protected_mutable (input : GeneralBorrowFreshMetadataChildMutableReuse.Input) (support : Nat → Prop) (lower upper : UInt64)
    (forest : GeneralBorrowForest.Forest (topology input.tree))
    (initial : OwnedOn (fun location => Profile input.tree location input.parent support) lower upper input.tree.locations) :
    OwnedOn (fun location => Profile (GeneralBorrowFreshMetadataChildMutableReuse.result input) location (GeneralBorrowFreshMetadataChildMutableReuse.index input)
      (extended support (GeneralBorrowFreshMetadataChildMutableReuse.index input))) lower upper (GeneralBorrowFreshMetadataChildMutableReuse.result input).locations := by
  let child := GeneralBorrowFreshMetadataChildMutableReuse.result input
  let index := GeneralBorrowFreshMetadataChildMutableReuse.index input
  let metadata := GeneralBorrowFreshMetadataChildMutableReuse.reuse input
  obtain ⟨node,present,_,_,_,_,notExposed⟩ := metadata.newNode
  have hidden : ∀ value, child.nodeAt index = some value → value.isExposed = false := by
    intro value found
    have equal := Option.some.inj (found.symm.trans present)
    exact equal ▸ notExposed
  have paths := GeneralBorrowFreshSharedPaths.of_reuse _ _ index.toNat input.parent.toNat
    (metadata.extension default default default) forest
  let predicate := fun location => Profile child location index (extended support index)
  have base : OwnedOn predicate lower upper input.tree.locations := by
    intro position valid positive beforeUpper afterLower
    exact reuse_location input.tree child index input.parent input.parentNode (GeneralBorrowFreshChild.child input.newTag input.parent)
      (GeneralBorrowFreshMetadataChildMutableReuse.mapping input) (GeneralBorrowFreshMetadataChildMutableReuse.locations input) support _ input.vacant input.parentPresent
      (GeneralBorrowFreshMetadataChildMutableReuse.shape input) (GeneralBorrowFreshMetadataChildMutableReuse.exposure input) paths hidden
      (initial position valid positive beforeUpper afterLower)
  have modified := modify_owned predicate lower upper input.tree.locations
    (Size.ofBytes input.offset) (Size.ofBytes input.len)
    (fun _ location => GeneralBorrowFreshMaterialization.materialized location index GeneralBorrowFreshChild.inside)
    input.well input.bounds base
    (fun _ location good => materialize child location index index GeneralBorrowFreshChild.inside _ hidden good)
  have rows := congrArg (fun shape => shape.2.2.1) (GeneralBorrowFreshMetadataChildMutableReuse.shape input)
  exact owned_shape child (GeneralBorrowFreshMetadataChildMutableReuse.stage input).locations child.locations index _ lower upper rows modified

end DuplicatePrefix.GeneralBorrowExposedInactiveReuseWindowConstructor
