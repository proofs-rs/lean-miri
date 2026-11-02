import duplicate_prefix.GeneralBorrowExposedConstructorAncestry
import duplicate_prefix.GeneralBorrowExposureChildAttach
import duplicate_prefix.GeneralBorrowExposureSifaTransport
namespace DuplicatePrefix.GeneralBorrowExposedConstructorUnique
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowView GeneralRangeMapState GeneralBorrowFreshGraph GeneralBorrowExposedConstructorAncestry
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
attribute [local irreducible] UniValMap.insert

/-- Raw initial effective permission of exposed component nodes, without a
hidden-component assumption or a successful-operation field. -/
def Unique (tree : BorrowTree) (location : LocationTree) (support : Nat → Prop) : Prop :=
  ∀ query node,support query.toNat → tree.nodeAt query=some node → node.isExposed=true →
    ((location.perms.get query).getD node.defaultLocationState).permission=.Unique

private theorem permission_same (before after : LocationTree) (query : UniIndex) (oldNode newNode : TreeNode)
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

theorem transport (before after : BorrowTree) (oldLocation newLocation : LocationTree) (support : Nat → Prop)
    (shape : treeShape after=treeShape before)
    (flags : GeneralBorrowFreshMetadataChildSifa.exposureShape after=GeneralBorrowFreshMetadataChildSifa.exposureShape before)
    (locations : locationShape newLocation=locationShape oldLocation)
    (initial : Unique before oldLocation support) : Unique after newLocation support := by
  intro query node member present exposed
  obtain ⟨old,found,_,_,_,defaults⟩ := GeneralBorrowFreshMetadata.node_fields after before shape.symm query node present
  change before.nodeAt query=some old at found
  have flag := GeneralBorrowFreshMetadataChildSifa.lookup_exposure before after flags query
  change (after.nodeAt query).map (fun node => node.isExposed)=(before.nodeAt query).map (fun node => node.isExposed) at flag
  rw [present,found] at flag
  have oldExposed : old.isExposed=true := (Option.some.inj flag).symm.trans exposed
  rw [permission_same oldLocation newLocation query old node locations defaults.symm]
  exact initial query old member found oldExposed

theorem attached (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat=tree.nodes.data.size) (parentPresent : tree.nodeAt parent=some parentNode)
    (hidden : newNode.isExposed=false) (location : LocationTree) (support : Nat → Prop)
    (initial : Unique tree location support) :
    Unique (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode) location (extended support index) := by
  intro query node member present exposed
  have different : query≠index := by
    intro same
    subst query
    rw [new_lookup tree index parent parentNode newNode atEnd parentPresent] at present
    cases present
    rw [hidden] at exposed
    cases exposed
  have oldMember : support query.toNat := by
    rcases member with same | old
    · exact False.elim (different (GeneralBorrowNodeUpdate.index_injective query index same))
    · exact old
  by_cases isParent : query=parent
  · subst query
    rw [parent_lookup tree index parent parentNode newNode atEnd parentPresent] at present
    cases present
    exact initial parent parentNode oldMember parentPresent exposed
  · rw [other_lookup tree index parent query parentNode newNode atEnd parentPresent isParent different] at present
    exact initial query node oldMember present exposed

theorem materialize (tree : BorrowTree) (location : LocationTree) (index : UniIndex) (inserted : LocationState)
    (support : Nat → Prop) (hidden : ∀ node,tree.nodeAt index=some node → node.isExposed=false)
    (initial : Unique tree location support) :
    Unique tree (GeneralBorrowFreshMaterialization.materialized location index inserted) support := by
  intro query node member present exposed
  have different : query≠index := by
    intro same
    subst query
    rw [hidden node present] at exposed
    cases exposed
  change (((location.perms.insert index inserted).get query).getD node.defaultLocationState).permission=.Unique
  rw [GeneralBorrowFreshLocation.get_other location.perms index query inserted different]
  exact initial query node member present exposed

theorem stage (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (mapping : UniKeyMap BorTag) (offset len : UInt64) (inserted : LocationState) (support : Nat → Prop)
    (atEnd : index.toNat=tree.nodes.data.size) (parentPresent : tree.nodeAt parent=some parentNode)
    (hidden : newNode.isExposed=false) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat)
    (initial : Every (fun location => Unique tree location support) tree.locations) :
    let next := GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode newNode mapping
      (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
        (fun _ location => GeneralBorrowFreshMaterialization.materialized location index inserted)).state
    Every (fun location => Unique next location (extended support index)) next.locations := by
  dsimp only
  let base := GeneralBorrowFreshGraph.attached tree index parent parentNode newNode
  let predicate := fun location => Unique base location (extended support index)
  have baseGood : Every predicate tree.locations := by
    intro position valid
    exact attached tree index parent parentNode newNode atEnd parentPresent hidden _ support (initial position valid)
  have newHidden : ∀ node,base.nodeAt index=some node → node.isExposed=false := by
    intro node present
    rw [new_lookup tree index parent parentNode newNode atEnd parentPresent] at present
    cases present
    exact hidden
  exact GeneralBorrowExposureChildAttach.modify_every predicate tree.locations (Size.ofBytes offset) (Size.ofBytes len)
    (fun _ location => GeneralBorrowFreshMaterialization.materialized location index inserted) well bounds baseGood
    (fun _ location good => materialize base location index inserted _ newHidden good)

theorem sifa (tree : BorrowTree) (start : UniIndex) (strongest : IdempotentForeignAccess) (support : Nat → Prop)
    (initial : Every (fun location => Unique tree location support) tree.locations) :
    let next := (sourceUpdateSifa tree start strongest).1
    Every (fun location => Unique next location support) next.locations := by
  dsimp only
  let next := (sourceUpdateSifa tree start strongest).1
  have shape := GeneralBorrowSifaView.preserves tree start strongest
  have flags := GeneralBorrowFreshMetadataChildSifa.sifa_exposure tree start strongest
  have locations := congrArg (fun shape => shape.2.2.1) shape
  change next.locations.entries.map (fun segment => (segment.range,locationShape segment.data))=
    tree.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) at locations
  have sizes : next.locations.entries.size=tree.locations.entries.size := by
    simpa only [Array.size_map] using congrArg Array.size locations
  change Every (fun location => Unique next location support) next.locations
  intro position valid
  have oldValid : position<tree.locations.entries.size := by rw [←sizes];exact valid
  have locationEq := congrArg (fun values => values[position]?) locations
  simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,Array.getElem?_eq_getElem oldValid,
    Option.map_some,Option.some.injEq,Prod.mk.injEq] at locationEq
  exact transport tree next _ _ support shape flags locationEq.2 (initial position oldValid)

theorem shared (input : GeneralBorrowFreshMetadataChildShared.Input) (support : Nat → Prop)
    (initial : Every (fun location => Unique input.tree location support) input.tree.locations) :
    Every (fun location => Unique (GeneralBorrowFreshMetadataChildShared.result input) location
      (extended support (GeneralBorrowFreshMetadataChildShared.index input))) (GeneralBorrowFreshMetadataChildShared.result input).locations := by
  have prepared := stage input.tree _ input.parent input.parentNode (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent) (GeneralBorrowFreshMetadataChildShared.mapping input)
    input.offset input.len GeneralBorrowFreshAnchor.sharedState support (GeneralBorrowFreshMetadataChildShared.at_end input)
    input.parentPresent rfl input.well input.bounds initial
  change Every (fun location => Unique (GeneralBorrowFreshMetadataChildShared.stage input) location _)
    (GeneralBorrowFreshMetadataChildShared.stage input).locations at prepared
  rw [GeneralBorrowFreshMetadataChildShared.tree_eq input]
  exact sifa (GeneralBorrowFreshMetadataChildShared.stage input) input.parent .Read _ prepared

theorem default_child (input : GeneralBorrowFreshMetadataChildDefault.Input) (support : Nat → Prop)
    (initial : Every (fun location => Unique input.tree location support) input.tree.locations) :
    Every (fun location => Unique (GeneralBorrowFreshMetadataChildDefault.result input) location
      (extended support (GeneralBorrowFreshMetadataChildDefault.index input))) (GeneralBorrowFreshMetadataChildDefault.result input).locations := by
  have prepared := stage input.tree _ input.parent input.parentNode (GeneralBorrowFreshDefaultChild.child input.newTag input.parent) (GeneralBorrowFreshMetadataChildDefault.mapping input)
    input.offset input.len GeneralBorrowFreshDefaultChild.inside support (GeneralBorrowFreshMetadataChildDefault.at_end input)
    input.parentPresent rfl input.well input.bounds initial
  change Every (fun location => Unique (GeneralBorrowFreshMetadataChildDefault.stage input) location _)
    (GeneralBorrowFreshMetadataChildDefault.stage input).locations at prepared
  rw [GeneralBorrowFreshMetadataChildDefault.tree_eq input]
  exact sifa (GeneralBorrowFreshMetadataChildDefault.stage input) input.parent .Read _ prepared
end DuplicatePrefix.GeneralBorrowExposedConstructorUnique
