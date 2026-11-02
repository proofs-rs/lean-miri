import duplicate_prefix.CurrentCallParentInsertion
import duplicate_prefix.CurrentCallResourceChild
import duplicate_prefix.GeneralBorrowSharedConstructorRuntime
import duplicate_prefix.GeneralBorrowSharedChildParentTagOrder
import duplicate_prefix.S05SharedConstructorDisjoint

/-! Actual shared (Frozen, unprotected) constructor metadata and the disjoint
current Bool-child authority frame over an OPTIONAL parent interpretation. -/
namespace DuplicatePrefix.CurrentCallSharedConstructorFrame
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership OrdinaryBorrowAuthority CurrentCallResourceNormalization
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardParentTagOrder
open GeneralBorrowView GeneralBorrowFreshGraph GeneralBorrowProjection GeneralRangeMapOrigins
open S05ConcreteProtectedChildCompletion
open S05CompletedAncestryReadMutable (Authority)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

private theorem physical_runtime (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node) :
    tree.tagMapping.get node.tag = some index ∧
    (∀ child, child ∈ node.children.toList ↔
      ∃ childNode, tree.nodes.get child = some childNode ∧ childNode.parent = some index) ∧
    (node.parent = none ↔ index ∈ tree.roots.toList) := by
  obtain ⟨forest⟩ := runtime.formed.forest default global.protectedTags
  obtain ⟨depth⟩ := runtime.formed.depth
  have reciprocal := GeneralBorrowExposedScopedReciprocal.of_forest tree default global.protectedTags forest depth
  refine ⟨runtime.formed.allocator.nodeTags index node present,?_,?_⟩
  · intro child
    constructor
    · intro member
      obtain ⟨childNode,childAt⟩ := runtime.formed.children index node present child member
      let topology := (source_normal_projection tree default global.protectedTags).topology
      have size : topology.nodes.size = tree.nodes.data.size := by
        unfold topology
        unfold_general_projection
        unfold_general_topology
        simp only [Array.size_map]
      have indexValid : index.toNat < topology.nodes.size := by
        rw [size]; exact GeneralBorrowNodeUpdate.lookup_valid _ _ _ present
      have childValid : child.toNat < topology.nodes.size := by
        rw [size]; exact GeneralBorrowNodeUpdate.lookup_valid _ _ _ childAt
      have parentProjection := projection_topology_node tree default global.protectedTags index.toNat index node rfl present
      have childProjection := projection_topology_node tree default global.protectedTags child.toNat child childNode rfl childAt
      change (topology.nodes[index.toNat]?.getD ⟨none,[]⟩) = _ at parentProjection
      change (topology.nodes[child.toNat]?.getD ⟨none,[]⟩) = _ at childProjection
      simp only [Array.getElem?_eq_getElem indexValid,Option.getD_some] at parentProjection
      simp only [Array.getElem?_eq_getElem childValid,Option.getD_some] at childProjection
      have projectedMember : child.toNat ∈ (topology.nodes[index.toNat]'indexValid).children := by
        rw [parentProjection]
        exact List.mem_map.mpr ⟨child,member,rfl⟩
      obtain ⟨valid,edge⟩ := forest.childParent index.toNat indexValid child.toNat projectedMember
      rw [childProjection] at edge
      have parentEq : childNode.parent = some index := by
        cases h : childNode.parent with
        | none => simp [h] at edge
        | some actual =>
          simp only [h,Option.map_some] at edge
          have same : actual = index := GeneralBorrowNodeUpdate.index_injective _ _ (Option.some.inj edge)
          exact congrArg some same
      exact ⟨childNode,childAt,parentEq⟩
    · rintro ⟨childNode,childAt,edge⟩
      obtain ⟨parentNode,parentAt,member⟩ := reciprocal child childNode childAt index edge
      have same : parentNode = node := Option.some.inj (parentAt.symm.trans present)
      simpa only [same] using member
  · constructor
    · exact runtime.formed.covered index node present
    · intro member
      obtain ⟨rootNode,rootAt,parentless⟩ := runtime.formed.rootNodes index member
      have same : node = rootNode := Option.some.inj (present.symm.trans rootAt)
      simpa only [same] using parentless

open GeneralBorrowView GeneralBorrowFreshGraph

set_option maxHeartbeats 200000 in
private theorem frame_of_stage (tree after : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts after global)
    (child parent : UniIndex) (parentNode : TreeNode) (newTag : BorTag)
    (vacant : tree.nodes.get child = none) (parentAt : tree.nodes.get parent = some parentNode)
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (shape : treeShape after = treeShape (GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
      (GeneralBorrowFreshAnchor.sharedNode newTag parent) mapping locations))
    (exposure : GeneralBorrowFreshMetadataChildSifa.exposureShape after =
      GeneralBorrowFreshMetadataChildSifa.exposureShape (GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
        (GeneralBorrowFreshAnchor.sharedNode newTag parent) mapping locations))
    (size : after.nodes.data.size = max tree.nodes.data.size (child.toNat+1))
    (roots : after.roots = tree.roots) : LeafFrame tree after child parent := by
  let stage := GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
    (GeneralBorrowFreshAnchor.sharedNode newTag parent) mapping locations
  have different : parent ≠ child := by
    intro same; rw [same,vacant] at parentAt; cases parentAt
  have parentStage : stage.nodes.get parent = some (updatedParent parentNode child) := by
    dsimp only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes,updatedParent]
    exact GeneralBorrowFreshLocation.get_same _ _ _
  have childStage : stage.nodes.get child = some (GeneralBorrowFreshAnchor.sharedNode newTag parent) := by
    dsimp only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes]
    rw [GeneralBorrowFreshLocation.get_other _ _ _ _ (Ne.symm different),GeneralBorrowFreshLocation.get_same]
  have otherStage : ∀ query, query ≠ parent → query ≠ child → stage.nodes.get query = tree.nodes.get query := by
    intro query notParent notChild
    dsimp only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes]
    rw [GeneralBorrowFreshLocation.get_other _ _ _ _ notParent,GeneralBorrowFreshLocation.get_other _ _ _ _ notChild]
  refine ⟨vacant,size,roots,⟨parentNode,parentAt⟩,?_,?_,?_,physical_runtime after global runtime⟩
  · obtain ⟨next,found,_,parentEq,_,_⟩ := GeneralBorrowFreshMetadata.node_fields stage after shape child _ childStage
    exact ⟨next,found,parentEq⟩
  · intro query node present
    have notChild : query ≠ child := by intro same; rw [same,vacant] at present; cases present
    have staged : ∃ stagedNode, stage.nodes.get query = some stagedNode ∧
        stagedNode.tag = node.tag ∧ stagedNode.parent = node.parent ∧ stagedNode.isExposed = node.isExposed := by
      by_cases same : query = parent
      · subst query
        have nodeEq : node = parentNode := Option.some.inj (present.symm.trans parentAt)
        subst node
        exact ⟨_,parentStage,rfl,rfl,rfl⟩
      · exact ⟨node,(otherStage query same notChild).trans present,rfl,rfl,rfl⟩
    obtain ⟨stagedNode,stagedAt,tagEq,parentEq,exposedEq⟩ := staged
    obtain ⟨next,found,tagAfter,parentAfter,_,_⟩ := GeneralBorrowFreshMetadata.node_fields stage after shape query stagedNode stagedAt
    have flags := GeneralBorrowFreshMetadataChildSifa.lookup_exposure stage after exposure query
    rw [found,stagedAt] at flags
    have sameExposure : next.isExposed = stagedNode.isExposed := by
      simpa only [Option.map_some,Option.some.injEq] using flags
    exact ⟨next,found,tagAfter.trans tagEq,parentAfter.trans parentEq,sameExposure.trans exposedEq⟩
  · intro query node present
    by_cases same : query = child
    · exact Or.inl same
    · right
      obtain ⟨stagedNode,stagedAt,_,parentEq,_,_⟩ := GeneralBorrowFreshMetadata.node_fields after stage shape.symm query node present
      by_cases isParent : query = parent
      · subst query
        have nodeEq : stagedNode = updatedParent parentNode child := Option.some.inj (stagedAt.symm.trans parentStage)
        exact ⟨parentNode,parentAt,by simpa only [nodeEq,updatedParent] using parentEq.symm⟩
      · exact ⟨stagedNode,(otherStage query isParent same).symm.trans stagedAt,parentEq.symm⟩


private theorem old_default_of_stage (tree after : BorrowTree) (child parent : UniIndex)
    (parentNode : TreeNode) (newTag : BorTag) (vacant : tree.nodes.get child=none)
    (parentAt : tree.nodes.get parent=some parentNode) (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (shape : treeShape after=treeShape (GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
      (GeneralBorrowFreshAnchor.sharedNode newTag parent) mapping locations))
    (query : UniIndex) (node : TreeNode) (present : tree.nodeAt query=some node) :
    ∃ next,after.nodeAt query=some next ∧ next.defaultInitialPermission=node.defaultInitialPermission := by
  let stage := GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
    (GeneralBorrowFreshAnchor.sharedNode newTag parent) mapping locations
  have notChild : query≠child := by
    intro same
    change tree.nodes.get query=some node at present
    rw [same,vacant] at present
    cases present
  have staged : ∃ previous,stage.nodes.get query=some previous ∧ previous.defaultInitialPermission=node.defaultInitialPermission := by
    by_cases isParent : query=parent
    · subst query
      have same : node=parentNode := Option.some.inj (present.symm.trans parentAt)
      subst node
      refine ⟨updatedParent parentNode child,?_,rfl⟩
      dsimp only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes]
      exact GeneralBorrowFreshLocation.get_same _ _ _
    · refine ⟨node,?_,rfl⟩
      dsimp only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes]
      rw [GeneralBorrowFreshLocation.get_other _ _ _ _ isParent,GeneralBorrowFreshLocation.get_other _ _ _ _ notChild]
      exact present
  obtain ⟨previous,previousAt,previousPermission⟩ := staged
  obtain ⟨next,nextAt,_,_,_,permission⟩ := GeneralBorrowFreshMetadata.node_fields stage after shape query previous previousAt
  exact ⟨next,nextAt,permission.trans previousPermission⟩

/-- Actual unprotected shared concrete constructor metadata, without a completed parent map. -/
theorem metadata (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (unheld : global.protectedTags.contains newTag = false)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen false
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child, actual.tree.indexOfTag newTag = some child ∧
        LeafFrame tree actual.tree child parent ∧
        ∀ query node,tree.nodeAt query=some node → ∃ next,actual.tree.nodeAt query=some next ∧
          next.tag=node.tag ∧ next.parent=node.parent ∧ next.isExposed=node.isExposed ∧
          next.defaultInitialPermission=node.defaultInitialPermission := by
  have output := GeneralBorrowSharedConstructorRuntime.construct tree global runtime parentTag newTag parent parentNode
    tagged present fresh room tagBound false unheld offset len nonzero bounds
  refine ⟨output.1,output.2.1,output.2.2.1,output.2.2.2,?_⟩
  let rank := GeneralBorrowStructuralHistoryShared.depth tree runtime.formed.toState
  let slot := GeneralBorrowStructuralHistoryShared.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,false,offset,len,nonzero,runtime.formed.well,bounds⟩
    let child := GeneralBorrowFreshMetadataChildShared.index input
    have data := GeneralBorrowFreshMetadataChildShared.append input
    have atEnd : child.toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildShared.at_end input
    have vacant : tree.nodes.get child = none := by
      simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _)]
    have size : (GeneralBorrowFreshMetadataChildShared.result input).nodes.data.size = max tree.nodes.data.size (child.toNat+1) := by
      change (GeneralBorrowFreshMetadataChildShared.result input).nodes.size = _
      rw [data.size,atEnd]
      change tree.nodes.data.size+1 = _
      omega
    have frame := frame_of_stage tree (GeneralBorrowFreshMetadataChildShared.result input) global output.2.1
      child parent parentNode newTag vacant present (GeneralBorrowFreshMetadataChildShared.mapping input)
      (GeneralBorrowFreshMetadataChildShared.locations input) (GeneralBorrowFreshMetadataChildShared.shape input)
      (GeneralBorrowFreshMetadataChildShared.exposure input) size data.roots
    refine ⟨child,data.freshLookup,frame,?_⟩
    intro query node oldAt
    obtain ⟨next,nextAt,tagEq,parentEq,exposureEq⟩ := frame.old query node oldAt
    obtain ⟨same,sameAt,permissionEq⟩ := old_default_of_stage tree (GeneralBorrowFreshMetadataChildShared.result input) child parent parentNode newTag
      vacant present (GeneralBorrowFreshMetadataChildShared.mapping input) (GeneralBorrowFreshMetadataChildShared.locations input) (GeneralBorrowFreshMetadataChildShared.shape input) query node oldAt
    have equal : next=same := Option.some.inj (nextAt.symm.trans sameAt)
    exact ⟨next,nextAt,tagEq,parentEq,exposureEq,equal.symm ▸ permissionEq⟩
  | reuse child available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        child,available,bounded,vacant,slack,false,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildSharedReuse.reuse input
    have size : (GeneralBorrowFreshMetadataChildSharedReuse.result input).nodes.data.size = max tree.nodes.data.size (child.toNat+1) := by
      change (GeneralBorrowFreshMetadataChildSharedReuse.result input).nodes.size = _
      rw [data.size]
      change tree.nodes.data.size = _
      omega
    have frame := frame_of_stage tree (GeneralBorrowFreshMetadataChildSharedReuse.result input) global output.2.1
      child parent parentNode newTag vacant present (GeneralBorrowFreshMetadataChildSharedReuse.mapping input)
      (GeneralBorrowFreshMetadataChildSharedReuse.locations input) (GeneralBorrowFreshMetadataChildSharedReuse.shape input)
      (GeneralBorrowFreshMetadataChildSharedReuse.exposure input) size data.roots
    refine ⟨child,data.freshLookup,frame,?_⟩
    intro query node oldAt
    obtain ⟨next,nextAt,tagEq,parentEq,exposureEq⟩ := frame.old query node oldAt
    obtain ⟨same,sameAt,permissionEq⟩ := old_default_of_stage tree (GeneralBorrowFreshMetadataChildSharedReuse.result input) child parent parentNode newTag
      vacant present (GeneralBorrowFreshMetadataChildSharedReuse.mapping input) (GeneralBorrowFreshMetadataChildSharedReuse.locations input) (GeneralBorrowFreshMetadataChildSharedReuse.shape input) query node oldAt
    have equal : next=same := Option.some.inj (nextAt.symm.trans sameAt)
    exact ⟨next,nextAt,tagEq,parentEq,exposureEq,equal.symm ▸ permissionEq⟩
private theorem lookup_shape (first second : LocationTree) (same : locationShape second = locationShape first)
    (index : UniIndex) : (second.perms.get index).map stateShape = (first.perms.get index).map stateShape := by
  have cell := congrArg (fun rows => rows[index.toNat]?) same
  simp only [locationShape,Array.getElem?_map] at cell
  have flat := congrArg (fun value : Option (Option StateShape) => value.getD none) cell
  unfold UniValMap.get
  cases firstAt : first.perms.data[index.toNat]? <;> cases secondAt : second.perms.data[index.toNat]? <;> simp_all

private theorem effective_shape (first second : LocationTree) (old next : TreeNode)
    (same : locationShape second = locationShape first)
    (permission : next.defaultInitialPermission = old.defaultInitialPermission) (index : UniIndex) :
    stateShape (RawState second index next) = stateShape (RawState first index old) := by
  have cell := lookup_shape first second same index
  unfold RawState
  cases oldAt : first.perms.get index <;> cases nextAt : second.perms.get index <;>
    simp_all [stateShape,TreeNode.defaultLocationState]

private theorem authority_state (old next : LocationState) (same : stateShape next = stateShape old)
    (held : Bool) :
    (LocalWrite next held ↔ LocalWrite old held) ∧ (ForeignWrite next held ↔ ForeignWrite old held) := by
  have permission := congrArg Prod.fst same
  have accessed := congrArg Prod.snd same
  simp only [stateShape] at permission accessed
  simp [LocalWrite,ForeignWrite,LocationState.possible,permission,accessed]


private theorem shape_authority (before after : BorrowTree) (completion : Completion)
    (held : ProtectedTags) (source : UniIndex) (first second : LocationTree)
    (nodes : treeShape after = treeShape before) (locations : locationShape second = locationShape first)
    (authority : Authority before completion held source first) :
    Authority after completion held source second := by
  intro index node present
  obtain ⟨old,oldAt,tag,parent,children,permission⟩ :=
    GeneralBorrowFreshMetadata.node_fields after before nodes.symm index node present
  have scalar := authority_state (RawState first index old) (RawState second index node)
    (effective_shape first second old node locations permission.symm index) (held.contains node.tag)
  have original := authority index old oldAt
  rw [tag] at original
  exact ⟨fun below => scalar.1.mpr (original.1 below),fun outside => scalar.2.mpr (original.2 outside)⟩

private theorem shape_owned (before after : BorrowTree) (completion : Completion)
    (held : ProtectedTags) (source : UniIndex) (lower upper : UInt64)
    (same : treeShape after = treeShape before)
    (owned : OwnedOn (Authority before completion held source) lower upper before.locations) :
    OwnedOn (Authority after completion held source) lower upper after.locations := by
  have entries := congrArg (fun shape => shape.2.2.1) same
  have sizes : after.locations.entries.size = before.locations.entries.size := by
    simpa only [treeShape,Array.size_map] using congrArg Array.size entries
  intro position valid positive lowerBound upperBound
  have oldValid : position < before.locations.entries.size := by omega
  have cell := congrArg (fun rows => rows[position]?) entries
  simp only [treeShape,Array.getElem?_map,Array.getElem?_eq_getElem valid,
    Array.getElem?_eq_getElem oldValid,Option.map_some,Option.some.injEq,Prod.mk.injEq] at cell
  have original := owned position oldValid positive (by simpa only [←cell.1] using lowerBound)
    (by simpa only [←cell.1] using upperBound)
  exact shape_authority before after completion held source _ _ same cell.2 original


/-- Every output segment overlapping the disjoint window is an unchanged
prepared value. Actual iterator splitting may change all segment indices. -/
private theorem modify_outside_owned (map : DedupRangeMap LocationTree) (offset len : Size)
    (well : map.WellFormed) (bounds : offset.bytes.toNat+len.bytes.toNat ≤ map.size.bytes.toNat)
    (modify : LocationTree → LocationTree) (idempotent : ∀ location, modify (modify location) = modify location)
    (P : LocationTree → Prop) (lower upper : UInt64)
    (disjoint : ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
      point.toNat < offset.bytes.toNat ∨ (offset.bytes+len.bytes).toNat ≤ point.toNat)
    (owned : OwnedOn P lower upper map) :
    OwnedOn P lower upper (map.modifyRange offset len (fun _ location => modify location)).state := by
  let prepared := map.iterMut offset len
  let changed := map.modifyRange offset len (fun _ location => modify location)
  have good := GeneralRangeMapOriginPrepare.iter_mut map offset len well bounds
  have preparedOwned := refines_owned_on map prepared.state P lower upper good.1.wellFormed good.2.1 owned
  have sizes : changed.state.entries.size = prepared.state.entries.size := by
    dsimp only [changed,prepared]
    rw [GeneralBorrowFreshModify.state_exact map offset len _ well bounds,GeneralBorrowFreshModify.fold_size]
  intro position valid positive start stop
  have oldValid : position < prepared.state.entries.size := by
    change position < changed.state.entries.size at valid
    omega
  obtain ⟨outputValid,entryEq⟩ := GeneralBorrowFreshModify.entry_exact map offset len (fun _ location => modify location)
    (fun _ location => idempotent location) well bounds position oldValid
  have rangeEq : (changed.state.entries[position]'valid).range = (prepared.state.entries[position]'oldValid).range := by
    have known := congrArg RangeMapSegment.range entryEq
    split at known <;> exact known
  rw [rangeEq] at start stop
  by_cases selected : position ∈ prepared.positions.toList
  · obtain ⟨cursor,bounded,same⟩ := Array.mem_iff_getElem.mp (Array.mem_def.mpr selected)
    have segmentValid : cursor < prepared.segments.size := by rw [←good.1.lengths];exact bounded
    have contained := good.2.2 cursor segmentValid
    have selectedEq := good.1.selected cursor bounded
    rw [selectedEq.2] at contained
    change offset.bytes.toNat ≤ prepared.state.entries[prepared.positions[cursor]].range.start.toNat ∧
      prepared.state.entries[prepared.positions[cursor]].range.stop.toNat ≤ (offset.bytes+len.bytes).toNat at contained
    simp only [same] at contained
    have segmentPositive := (GeneralRangeMapGeometry.facts prepared.state good.1.wellFormed (by omega)).2.1 position oldValid
    by_cases earlier : lower.toNat ≤ prepared.state.entries[position].range.start.toNat
    · have outside := disjoint prepared.state.entries[position].range.start earlier start
      exact False.elim (by omega)
    · have outside := disjoint lower (Nat.le_refl _) positive
      exact False.elim (by omega)
  · simp only [show ¬position ∈ (map.iterMut offset len).positions.toList from selected,↓reduceIte] at entryEq
    rw [entryEq]
    exact preparedOwned position oldValid positive start stop

private theorem no_vacant_ancestor (tree : BorrowTree) (completion : Completion)
    (complete : ParentInterpretation tree completion) (child target : UniIndex)
    (vacant : tree.nodes.get child = none) (live : ∃ node, tree.nodes.get target = some node)
    (path : Below completion child target) : False := by
  induction path with
  | refl => obtain ⟨node,present⟩ := live; rw [vacant] at present; cases present
  | @step predecessor target edge path induction =>
    exact induction ((complete.edgeLive target predecessor edge).2)

private theorem stage_location (tree : BorrowTree) (completion : Completion) (held : ProtectedTags)
    (complete : ParentInterpretation tree completion) (child parent target : UniIndex) (parentNode targetNode : TreeNode) (tag : BorTag)
    (vacant : tree.nodes.get child = none) (parentAt : tree.nodes.get parent = some parentNode)
    (targetAt : tree.nodes.get target = some targetNode)
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree) (location : LocationTree)
    (clean : location.perms.get child = none)
    (authority : Authority tree completion held target location) :
    Authority (GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
      (GeneralBorrowFreshAnchor.sharedNode tag parent) mapping locations) (extend completion child parent) held target location := by
  intro index node present
  by_cases new : index = child
  · subst index
    dsimp only [GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,
      GeneralBorrowFreshNode.attachedNodes] at present
    have different : parent ≠ child := by intro same; rw [same,vacant] at parentAt; cases parentAt
    rw [GeneralBorrowFreshLocation.get_other _ _ _ _ (Ne.symm different),GeneralBorrowFreshLocation.get_same] at present
    have nodeEq : node = GeneralBorrowFreshAnchor.sharedNode tag parent := Option.some.inj present.symm
    have outside : ¬Below (extend completion child parent) child target := by
      intro path
      exact no_vacant_ancestor tree completion complete child target vacant ⟨targetNode,targetAt⟩
        ((CurrentCallResourceChild.old_ancestry_iff tree completion complete child parent vacant ⟨targetNode,targetAt⟩).mp path)
    constructor
    · intro impossible; exact False.elim (outside impossible)
    · intro _
      simp [RawState,clean,nodeEq,GeneralBorrowFreshAnchor.sharedNode,TreeNode.defaultLocationState,
        ForeignWrite,LocationState.possible,Permission.isUnique]
  · have old : ∃ old, tree.nodes.get index = some old ∧ node.tag = old.tag ∧
        node.defaultInitialPermission = old.defaultInitialPermission := by
      dsimp only [GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,
        GeneralBorrowFreshNode.attachedNodes] at present
      by_cases isParent : index = parent
      · subst index
        rw [GeneralBorrowFreshLocation.get_same] at present
        have same : node = {parentNode with children := parentNode.children.push child} := Option.some.inj present.symm
        exact ⟨parentNode,parentAt,by rw [same],by rw [same]⟩
      · rw [GeneralBorrowFreshLocation.get_other _ _ _ _ isParent,
          GeneralBorrowFreshLocation.get_other _ _ _ _ new] at present
        exact ⟨node,present,rfl,rfl⟩
    obtain ⟨old,oldAt,tagEq,defaultEq⟩ := old
    have effective : stateShape (RawState location index node) = stateShape (RawState location index old) := by
      unfold RawState
      cases location.perms.get index <;> simp [stateShape,TreeNode.defaultLocationState,defaultEq]
    have scalar := authority_state _ _ effective (held.contains node.tag)
    have original := authority index old oldAt
    rw [←tagEq] at original
    have ancestry := CurrentCallResourceChild.old_ancestry_iff tree completion complete child parent vacant ⟨targetNode,targetAt⟩ (ancestor := index)
    exact ⟨fun below => scalar.1.mpr (original.1 (ancestry.mp below)),
      fun outside => scalar.2.mpr (original.2 (fun below => outside (ancestry.mpr below)))⟩

private theorem stage_owned (tree : BorrowTree) (completion : Completion) (held : ProtectedTags)
    (complete : ParentInterpretation tree completion) (child parent target : UniIndex) (parentNode targetNode : TreeNode) (tag : BorTag)
    (vacant : tree.nodes.get child = none) (parentAt : tree.nodes.get parent = some parentNode)
    (targetAt : tree.nodes.get target = some targetNode)
    (mapping : UniKeyMap BorTag) (offset len lower upper : UInt64) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (disjoint : ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
      point.toNat < offset.toNat ∨ (offset+len).toNat ≤ point.toNat)
    (clean : ∀ position (valid : position < tree.locations.entries.size), tree.locations.entries[position].data.perms.get child = none)
    (owned : OwnedOn (Authority tree completion held target) lower upper tree.locations) :
    let locations := (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
      (fun _ location => GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshAnchor.sharedState)).state
    let stage := GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
      (GeneralBorrowFreshAnchor.sharedNode tag parent) mapping locations
    OwnedOn (Authority stage (extend completion child parent) held target) lower upper locations := by
  let locations := (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
    (fun _ location => GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshAnchor.sharedState)).state
  have initial : OwnedOn (fun location => Authority tree completion held target location ∧ location.perms.get child = none)
      lower upper tree.locations := by
    intro position valid positive start stop
    exact ⟨owned position valid positive start stop,clean position valid⟩
  have unchanged := modify_outside_owned tree.locations (Size.ofBytes offset) (Size.ofBytes len) well bounds
    (fun location => GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshAnchor.sharedState)
    (fun location => GeneralBorrowFreshInstallation.materialized_idempotent location child GeneralBorrowFreshAnchor.sharedState)
    _ lower upper disjoint initial
  dsimp only
  intro position valid positive start stop
  obtain ⟨oldAuthority,oldClean⟩ := unchanged position valid positive start stop
  exact stage_location tree completion held complete child parent target parentNode targetNode tag vacant parentAt targetAt
    mapping locations _ oldClean oldAuthority

/-- The old target may inhabit the SAME allocation as the source window.
Only byte-window disjointness is required. The fresh shared child is a
foreign inactive frozen node at these bytes, and old ancestry remains exact. -/
theorem disjoint (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : ParentInterpretation tree completion)
    (parentTag newTag : BorTag) (parent target : UniIndex) (parentNode targetNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (targetAt : tree.nodes.get target = some targetNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (held : Bool) (aligned : global.protectedTags.contains newTag = held)
    (offset len lower upper : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (disjoint : ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
      point.toNat < offset.toNat ∨ (offset+len).toNat ≤ point.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags target) lower upper tree.locations) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen held
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child, actual.tree.indexOfTag newTag = some child ∧
        OwnedOn (Authority actual.tree (extend completion child parent) global.protectedTags target)
          lower upper actual.tree.locations := by
  obtain ⟨done,afterRuntime,capacity,growth⟩ := GeneralBorrowSharedConstructorRuntime.construct
    tree global runtime parentTag newTag parent parentNode tagged present fresh room tagBound held aligned offset len nonzero bounds
  obtain ⟨child,lookup,_,_⟩ := GeneralBorrowSharedChildGraph.construct
    tree global runtime parentTag newTag parent parentNode tagged present fresh room held offset len nonzero bounds
  refine ⟨done,afterRuntime,capacity,growth,child,lookup,?_⟩
  let rank := GeneralBorrowStructuralHistoryShared.depth tree runtime.formed.toState
  let slot := GeneralBorrowStructuralHistoryShared.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,held,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildShared.append input
    have same : GeneralBorrowFreshMetadataChildShared.index input = child := Option.some.inj (data.freshLookup.symm.trans lookup)
    have atEnd : (GeneralBorrowFreshMetadataChildShared.index input).toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildShared.at_end input
    have vacant : tree.nodes.get (GeneralBorrowFreshMetadataChildShared.index input) = none := by
      simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _)]
    have clean : ∀ position (valid : position < tree.locations.entries.size),
        tree.locations.entries[position].data.perms.get (GeneralBorrowFreshMetadataChildShared.index input) = none := by
      intro position valid
      exact (runtime.formed.profile position valid).vacant _ vacant
    have staged := stage_owned tree completion global.protectedTags complete (GeneralBorrowFreshMetadataChildShared.index input)
      parent target parentNode targetNode newTag vacant present targetAt (GeneralBorrowFreshMetadataChildShared.mapping input)
      offset len lower upper runtime.formed.well bounds disjoint clean owned
    have result := shape_owned (GeneralBorrowFreshMetadataChildShared.stage input)
      (GeneralBorrowFreshMetadataChildShared.result input) _ global.protectedTags target
      lower upper (GeneralBorrowFreshMetadataChildShared.shape input) staged
    rw [same] at result
    simpa only [GeneralBorrowFreshMetadataChildShared.result,input] using result
  | reuse index available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        index,available,bounded,vacant,slack,held,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildSharedReuse.reuse input
    have same : index = child := Option.some.inj (data.freshLookup.symm.trans lookup)
    have clean : ∀ position (valid : position < tree.locations.entries.size),
        tree.locations.entries[position].data.perms.get index = none := by
      intro position valid
      exact (runtime.formed.profile position valid).vacant _ vacant
    have staged := stage_owned tree completion global.protectedTags complete index parent target parentNode targetNode newTag vacant present targetAt
      (GeneralBorrowFreshMetadataChildSharedReuse.mapping input) offset len lower upper runtime.formed.well bounds disjoint clean owned
    have result := shape_owned (GeneralBorrowFreshMetadataChildSharedReuse.stage input)
      (GeneralBorrowFreshMetadataChildSharedReuse.result input) _ global.protectedTags target
      lower upper (GeneralBorrowFreshMetadataChildSharedReuse.shape input) staged
    rw [same] at result
    simpa only [GeneralBorrowFreshMetadataChildSharedReuse.result,input] using result

/-- Immediate optional-parent-map consumer of actual shared constructor metadata and the disjoint Bool frame. -/
theorem construct (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : ParentInterpretation tree completion)
    (parentTag newTag : BorTag) (parent target : UniIndex) (parentNode targetNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (targetAt : tree.nodes.get target = some targetNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (unheld : global.protectedTags.contains newTag = false)
    (offset len lower upper : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (apart : ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
      point.toNat < offset.toNat ∨ (offset+len).toNat ≤ point.toNat)
    (primaryLive : ∃ node,tree.nodes.get allocationRoot=some node)
    (parentOrder : parentNode.tag.value ≤ newTag.value)
    (owned : OwnedOn (Authority tree completion global.protectedTags target) lower upper tree.locations) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen false
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child, actual.tree.indexOfTag newTag = some child ∧ LeafFrame tree actual.tree child parent ∧
        ParentInterpretation actual.tree (extend completion child parent) ∧
        OwnedOn (Authority actual.tree (extend completion child parent) global.protectedTags target)
          lower upper actual.tree.locations ∧
        (∀ query node,tree.nodeAt query=some node → ∃ next,actual.tree.nodeAt query=some next ∧
          next.tag=node.tag ∧ next.parent=node.parent ∧ next.isExposed=node.isExposed ∧
          next.defaultInitialPermission=node.defaultInitialPermission) := by
  obtain ⟨done,afterRuntime,capacity,growth,child,lookup,leaf,old⟩ := metadata tree global runtime
    parentTag newTag parent parentNode tagged present fresh room tagBound unheld offset len nonzero bounds
  obtain ⟨_,_,_,_,framedChild,framedLookup,framed⟩ := disjoint tree global completion runtime complete
    parentTag newTag parent target parentNode targetNode tagged present targetAt fresh room tagBound false unheld
    offset len lower upper nonzero bounds apart owned
  have same : framedChild=child := Option.some.inj (framedLookup.symm.trans lookup)
  subst framedChild
  have order := GeneralBorrowSharedChildParentTagOrder.construct tree global runtime parentTag newTag parent parentNode
    tagged present fresh room false offset len nonzero bounds complete.order parentOrder
  have parents := CurrentCallParentInsertion.of_leaf tree _ completion complete child parent leaf primaryLive afterRuntime.formed.toGraphState order
  exact ⟨done,afterRuntime,capacity,growth,child,lookup,leaf,parents,framed,old⟩


end
end DuplicatePrefix.CurrentCallSharedConstructorFrame
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallSharedConstructorFrame" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved optional shared constructor dependency {dependency}"
