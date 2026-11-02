import duplicate_prefix.GeneralBorrowExposedConstructorUnique
import duplicate_prefix.GeneralBorrowExposedScopedInactiveExposurePermission
namespace DuplicatePrefix.GeneralBorrowExposedInactiveConstructor
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowView GeneralRangeMapState GeneralBorrowFreshGraph GeneralBorrowExposedConstructorAncestry
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
attribute [local irreducible] UniValMap.insert

/-- Exposed pointers retained in the selected component are either active
Unique ancestors or inactive Disabled offpath nodes. Disabled handles remain
physically present; they are not silently discarded or made usable. -/
def Profile (tree : BorrowTree) (location : LocationTree) (anchor : UniIndex) (support : Nat → Prop) : Prop :=
  ∀ query node,support query.toNat → tree.nodeAt query=some node → node.isExposed=true →
    (query.toNat ∈ (topology tree).ancestorPath anchor.toNat ∧
      ((location.perms.get query).getD node.defaultLocationState).permission=.Unique) ∨
    (query.toNat ∉ (topology tree).ancestorPath anchor.toNat ∧
      ((location.perms.get query).getD node.defaultLocationState).permission=.Disabled)

theorem permission_same (before after : LocationTree) (query : UniIndex) (oldNode newNode : TreeNode)
    (same : locationShape after=locationShape before)
    (defaults : newNode.defaultInitialPermission=oldNode.defaultInitialPermission) :
    ((after.perms.get query).getD newNode.defaultLocationState).permission=
      ((before.perms.get query).getD oldNode.defaultLocationState).permission := by
  have states : (after.perms.get query).map stateShape=(before.perms.get query).map stateShape := by
    have map_get (nodes : UniValMap LocationState) :
        (UniValMap.get ⟨nodes.data.map (Option.map stateShape)⟩ query)=(nodes.get query).map stateShape := by
      simp only [UniValMap.get,Array.getElem?_map]
      cases nodes.data[query.toNat]? <;> rfl
    rw [←map_get after.perms,←map_get before.perms]
    exact congrArg (fun values => UniValMap.get ⟨values⟩ query) same
  cases old : before.perms.get query <;> cases new : after.perms.get query
  · exact defaults
  · simp only [old,new,Option.map_none,Option.map_some] at states;cases states
  · simp only [old,new,Option.map_none,Option.map_some] at states;cases states
  · simp only [old,new,Option.map_some] at states
    exact congrArg Prod.fst (Option.some.inj states)

theorem location_transport (tree : BorrowTree) (before after : LocationTree) (anchor : UniIndex) (support : Nat → Prop)
    (same : locationShape after=locationShape before) (initial : Profile tree before anchor support) :
    Profile tree after anchor support := by
  intro query node member present exposed
  rw [permission_same before after query node node same rfl]
  exact initial query node member present exposed

theorem old_default (tree after : BorrowTree) (index parent query : UniIndex) (parentNode newNode oldNode node : TreeNode)
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (atEnd : index.toNat=tree.nodes.data.size) (parentPresent : tree.nodeAt parent=some parentNode)
    (same : treeShape after=treeShape (GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode newNode mapping locations))
    (different : query≠index) (oldPresent : tree.nodeAt query=some oldNode) (present : after.nodeAt query=some node) :
    node.defaultInitialPermission=oldNode.defaultInitialPermission := by
  let stage := GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode newNode mapping locations
  have staged : ∃ value,stage.nodeAt query=some value ∧ value.defaultInitialPermission=oldNode.defaultInitialPermission := by
    by_cases isParent : query=parent
    · subst query
      have equal : oldNode=parentNode := Option.some.inj (oldPresent.symm.trans parentPresent)
      subst oldNode
      exact ⟨updatedParent parentNode index,parent_lookup tree index parent parentNode newNode atEnd parentPresent,rfl⟩
    · exact ⟨oldNode,(other_lookup tree index parent query parentNode newNode atEnd parentPresent isParent different).trans oldPresent,rfl⟩
  obtain ⟨value,found,permission⟩ := staged
  obtain ⟨next,lookup,_,_,_,defaultEq⟩ := GeneralBorrowFreshMetadata.node_fields stage after same query value found
  have equal : node=next := Option.some.inj (present.symm.trans lookup)
  exact equal ▸ defaultEq.trans permission

theorem append_location (tree after : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree) (support : Nat → Prop) (location : LocationTree)
    (atEnd : index.toNat=tree.nodes.data.size) (parentPresent : tree.nodeAt parent=some parentNode)
    (shape : treeShape after=treeShape (GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode newNode mapping locations))
    (flags : GeneralBorrowFreshMetadataChildSifa.exposureShape after=
      GeneralBorrowFreshMetadataChildSifa.exposureShape (GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode newNode mapping locations))
    (paths : GeneralBorrowFreshSharedPaths.Attach (topology tree) (topology after) parent.toNat index.toNat)
    (hidden : ∀ node,after.nodeAt index=some node → node.isExposed=false)
    (initial : Profile tree location parent support) : Profile after location index (extended support index) := by
  intro query node member present exposed
  have different : query≠index := by intro same;subst query;rw [hidden node present] at exposed;cases exposed
  have natDifferent : query.toNat≠index.toNat := by intro same;exact different (GeneralBorrowNodeUpdate.index_injective query index same)
  have oldMember : support query.toNat := by
    rcases member with fresh | old
    · exact False.elim (natDifferent fresh)
    · exact old
  obtain ⟨old,found,oldExposed⟩ := GeneralBorrowExposedConstructorAncestry.old_exposed tree after index parent query parentNode newNode node mapping locations
    atEnd parentPresent flags different present exposed
  have defaultEq := old_default tree after index parent query parentNode newNode old node mapping locations atEnd parentPresent shape different found present
  have permissions := permission_same location location query old node rfl defaultEq
  rw [permissions]
  have original := initial query old oldMember found oldExposed
  rw [paths.childPath]
  rcases original with active | inactive
  · exact Or.inl ⟨List.mem_cons_of_mem index.toNat active.1,active.2⟩
  · exact Or.inr ⟨by simpa only [List.mem_cons,not_or] using And.intro natDifferent inactive.1,inactive.2⟩

theorem materialize (tree : BorrowTree) (location : LocationTree) (anchor index : UniIndex) (inserted : LocationState)
    (support : Nat → Prop) (hidden : ∀ node,tree.nodeAt index=some node → node.isExposed=false)
    (initial : Profile tree location anchor support) :
    Profile tree (GeneralBorrowFreshMaterialization.materialized location index inserted) anchor support := by
  intro query node member present exposed
  have different : query≠index := by intro same;subst query;rw [hidden node present] at exposed;cases exposed
  change (_ ∧ (((location.perms.insert index inserted).get query).getD node.defaultLocationState).permission=_) ∨
    (_ ∧ (((location.perms.insert index inserted).get query).getD node.defaultLocationState).permission=_)
  rw [GeneralBorrowFreshLocation.get_other location.perms index query inserted different]
  exact initial query node member present exposed

theorem every_shape (tree : BorrowTree) (before after : DedupRangeMap LocationTree) (anchor : UniIndex) (support : Nat → Prop)
    (same : after.entries.map (fun segment => (segment.range,locationShape segment.data))=
      before.entries.map (fun segment => (segment.range,locationShape segment.data)))
    (initial : Every (fun location => Profile tree location anchor support) before) :
    Every (fun location => Profile tree location anchor support) after := by
  have sizes : after.entries.size=before.entries.size := by simpa only [Array.size_map] using congrArg Array.size same
  intro position valid
  have oldValid : position<before.entries.size := by rw [←sizes];exact valid
  have locationEq := congrArg (fun values => values[position]?) same
  simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,Array.getElem?_eq_getElem oldValid,
    Option.map_some,Option.some.injEq,Prod.mk.injEq] at locationEq
  exact location_transport tree _ _ anchor support locationEq.2 (initial position oldValid)

/-- Actual Shared construction preserves active and inactive exposed handles
through range materialization and source SIFA, on arbitrary partitions. -/
theorem shared (input : GeneralBorrowFreshMetadataChildShared.Input) (support : Nat → Prop)
    (forest : GeneralBorrowForest.Forest (topology input.tree))
    (initial : Every (fun location => Profile input.tree location input.parent support) input.tree.locations) :
    Every (fun location => Profile (GeneralBorrowFreshMetadataChildShared.result input) location (GeneralBorrowFreshMetadataChildShared.index input)
      (extended support (GeneralBorrowFreshMetadataChildShared.index input))) (GeneralBorrowFreshMetadataChildShared.result input).locations := by
  let child := GeneralBorrowFreshMetadataChildShared.result input
  let index := GeneralBorrowFreshMetadataChildShared.index input
  let metadata := GeneralBorrowFreshMetadataChildShared.append input
  obtain ⟨node,present,_,_,_,_,notExposed⟩ := metadata.newNode
  have hidden : ∀ value,child.nodeAt index=some value → value.isExposed=false := by
    intro value found
    have equal : value=node := Option.some.inj (found.symm.trans present)
    exact equal ▸ notExposed
  have size : (topology input.tree).nodes.size=index.toNat := by
    rw [GeneralBorrowFreshMetadataChildShared.at_end]
    unfold topology
    unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
  have paths := GeneralBorrowFreshSharedPaths.of_append _ _ input.parent.toNat (metadata.extension default default default) forest
  change GeneralBorrowFreshSharedPaths.Attach (topology input.tree) (topology child) input.parent.toNat (topology input.tree).nodes.size at paths
  rw [size] at paths
  let predicate := fun location => Profile child location index (extended support index)
  have base : Every predicate input.tree.locations := by
    intro position valid
    exact append_location input.tree child index input.parent input.parentNode (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent)
      (GeneralBorrowFreshMetadataChildShared.mapping input) (GeneralBorrowFreshMetadataChildShared.locations input) support _ (GeneralBorrowFreshMetadataChildShared.at_end input)
      input.parentPresent (GeneralBorrowFreshMetadataChildShared.shape input) (GeneralBorrowFreshMetadataChildShared.exposure input) paths hidden (initial position valid)
  have modified := GeneralBorrowExposureChildAttach.modify_every predicate input.tree.locations
    (Size.ofBytes input.offset) (Size.ofBytes input.len)
    (fun _ location => GeneralBorrowFreshMaterialization.materialized location index GeneralBorrowFreshAnchor.sharedState) input.well input.bounds base
    (fun _ location good => materialize child location index index GeneralBorrowFreshAnchor.sharedState _ hidden good)
  have rows := congrArg (fun shape => shape.2.2.1) (GeneralBorrowFreshMetadataChildShared.shape input)
  exact every_shape child (GeneralBorrowFreshMetadataChildShared.stage input).locations child.locations index _ rows modified

/-- Actual Default construction preserves active and inactive exposed handles
through range materialization and source SIFA, on arbitrary partitions. -/
theorem default_child (input : GeneralBorrowFreshMetadataChildDefault.Input) (support : Nat → Prop)
    (forest : GeneralBorrowForest.Forest (topology input.tree))
    (initial : Every (fun location => Profile input.tree location input.parent support) input.tree.locations) :
    Every (fun location => Profile (GeneralBorrowFreshMetadataChildDefault.result input) location (GeneralBorrowFreshMetadataChildDefault.index input)
      (extended support (GeneralBorrowFreshMetadataChildDefault.index input))) (GeneralBorrowFreshMetadataChildDefault.result input).locations := by
  let child := GeneralBorrowFreshMetadataChildDefault.result input
  let index := GeneralBorrowFreshMetadataChildDefault.index input
  let metadata := GeneralBorrowFreshMetadataChildDefault.append input
  obtain ⟨node,present,_,_,_,_,notExposed⟩ := metadata.newNode
  have hidden : ∀ value,child.nodeAt index=some value → value.isExposed=false := by
    intro value found
    have equal : value=node := Option.some.inj (found.symm.trans present)
    exact equal ▸ notExposed
  have size : (topology input.tree).nodes.size=index.toNat := by
    rw [GeneralBorrowFreshMetadataChildDefault.at_end]
    unfold topology
    unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
  have paths := GeneralBorrowFreshSharedPaths.of_append _ _ input.parent.toNat (metadata.extension default default default) forest
  change GeneralBorrowFreshSharedPaths.Attach (topology input.tree) (topology child) input.parent.toNat (topology input.tree).nodes.size at paths
  rw [size] at paths
  let predicate := fun location => Profile child location index (extended support index)
  have base : Every predicate input.tree.locations := by
    intro position valid
    exact append_location input.tree child index input.parent input.parentNode (GeneralBorrowFreshDefaultChild.child input.newTag input.parent)
      (GeneralBorrowFreshMetadataChildDefault.mapping input) (GeneralBorrowFreshMetadataChildDefault.locations input) support _ (GeneralBorrowFreshMetadataChildDefault.at_end input)
      input.parentPresent (GeneralBorrowFreshMetadataChildDefault.shape input) (GeneralBorrowFreshMetadataChildDefault.exposure input) paths hidden (initial position valid)
  have modified := GeneralBorrowExposureChildAttach.modify_every predicate input.tree.locations
    (Size.ofBytes input.offset) (Size.ofBytes input.len)
    (fun _ location => GeneralBorrowFreshMaterialization.materialized location index GeneralBorrowFreshDefaultChild.inside) input.well input.bounds base
    (fun _ location good => materialize child location index index GeneralBorrowFreshDefaultChild.inside _ hidden good)
  have rows := congrArg (fun shape => shape.2.2.1) (GeneralBorrowFreshMetadataChildDefault.shape input)
  exact every_shape child (GeneralBorrowFreshMetadataChildDefault.stage input).locations child.locations index _ rows modified

end DuplicatePrefix.GeneralBorrowExposedInactiveConstructor
