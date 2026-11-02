import duplicate_prefix.CurrentCallSharedReference
import duplicate_prefix.CurrentCallResourceDefaultShared
import duplicate_prefix.CurrentCallParentInsertion
import duplicate_prefix.CurrentCallResourceChild
import duplicate_prefix.GeneralBorrowRawDefaultExpression
import duplicate_prefix.GeneralBorrowDefaultCapabilityConstructor
import duplicate_prefix.GeneralBorrowDefaultChildMetadata
import duplicate_prefix.GeneralBorrowDefaultChildOrder
import duplicate_prefix.GeneralBorrowRawTargetActivity
import duplicate_prefix.GeneralBorrowDefaultConstructorRuntime
import duplicate_prefix.GeneralBorrowStructuralHistoryDefault
import duplicate_prefix.S05ConcreteProtectedChildAuthority

/-! Actual Default mutable reborrowing from current completed raw ownership.
The constructor and its exact raw tables are derived from the current machine,
not a legacy Positive packet or an assumed successful callback. -/
namespace DuplicatePrefix.CurrentCallResourceDefaultMutable
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Input Miri.Interpreter
open CandidateStableCallOwnership GeneralBorrowProjection OrdinaryBorrowAuthority
open S05ConcreteProtectedChildCompletion S05CompletedAncestryReadMutable
open CanonicalConfigFacts ActualReferenceContext
open GeneralBorrowRawDefaultExpression RootReferenceInfo RootReferenceTrees
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality
open GeneralRangeMapOrigins GeneralRangeMapState CurrentCallResourceNormalization
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

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
private theorem default_frame (tree after : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts after global)
    (child parent : UniIndex) (parentNode : TreeNode) (newTag : BorTag)
    (vacant : tree.nodes.get child = none) (parentAt : tree.nodes.get parent = some parentNode)
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (shape : treeShape after = treeShape (GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
      (GeneralBorrowFreshDefaultChild.child newTag parent) mapping locations))
    (exposure : GeneralBorrowFreshMetadataChildSifa.exposureShape after =
      GeneralBorrowFreshMetadataChildSifa.exposureShape (GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
        (GeneralBorrowFreshDefaultChild.child newTag parent) mapping locations))
    (size : after.nodes.data.size = max tree.nodes.data.size (child.toNat+1))
    (roots : after.roots = tree.roots) : LeafFrame tree after child parent := by
  let stage := GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
    (GeneralBorrowFreshDefaultChild.child newTag parent) mapping locations
  have different : parent ≠ child := by
    intro same; rw [same,vacant] at parentAt; cases parentAt
  have parentStage : stage.nodes.get parent = some (updatedParent parentNode child) := by
    dsimp only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes,updatedParent]
    exact GeneralBorrowFreshLocation.get_same _ _ _
  have childStage : stage.nodes.get child = some (GeneralBorrowFreshDefaultChild.child newTag parent) := by
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

/-- Actual concrete protected child construction extends the SAME completed
origin assignment, including sparse vacant-slot reuse. The input runtime/tree
is the post-parent-Read state; no callback Positive or future rights are inputs. -/
private theorem old_default_of_stage (tree after : BorrowTree) (child parent : UniIndex)
    (parentNode : TreeNode) (newTag : BorTag) (vacant : tree.nodes.get child=none)
    (parentAt : tree.nodes.get parent=some parentNode) (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (shape : treeShape after=treeShape (GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
      (GeneralBorrowFreshDefaultChild.child newTag parent) mapping locations))
    (query : UniIndex) (node : TreeNode) (present : tree.nodeAt query=some node) :
    ∃ next,after.nodeAt query=some next ∧ next.defaultInitialPermission=node.defaultInitialPermission := by
  let stage := GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
    (GeneralBorrowFreshDefaultChild.child newTag parent) mapping locations
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

private theorem completion_construct (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : ParentInterpretation tree completion)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (unheld : global.protectedTags.contains newTag = false)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (primaryLive : ∃ node,tree.nodes.get allocationRoot=some node)
    (parentOrder : parentNode.tag.value≤newTag.value) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child, actual.tree.indexOfTag newTag = some child ∧
        S05ConcreteProtectedChildCompletion.LeafFrame tree actual.tree child parent ∧ ParentInterpretation actual.tree (extend completion child parent) ∧
        (∀ ancestor, Below completion ancestor parent → Below (extend completion child parent) ancestor child) ∧
        (∀ query node,tree.nodes.get query=some node →∃ next,actual.tree.nodes.get query=some next ∧
          next.defaultInitialPermission=node.defaultInitialPermission) := by
  have output := GeneralBorrowDefaultConstructorRuntime.construct tree global runtime parentTag newTag parent parentNode
    tagged present fresh room tagBound unheld offset len nonzero bounds
  have resultOrder:=GeneralBorrowDefaultChildOrder.construct tree global runtime complete.order parentTag newTag parent parentNode
    tagged present fresh room parentOrder offset len nonzero bounds
  refine ⟨output.1,output.2.1,output.2.2.1,output.2.2.2,?_⟩
  let rank := GeneralBorrowStructuralHistoryDefault.depth tree runtime.formed.toState
  let slot := GeneralBorrowStructuralHistoryDefault.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildDefault.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
    let child := GeneralBorrowFreshMetadataChildDefault.index input
    have data := GeneralBorrowFreshMetadataChildDefault.append input
    have atEnd : child.toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildDefault.at_end input
    have vacant : tree.nodes.get child = none := by
      simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _)]
    have size : (GeneralBorrowFreshMetadataChildDefault.result input).nodes.data.size = max tree.nodes.data.size (child.toNat+1) := by
      change (GeneralBorrowFreshMetadataChildDefault.result input).nodes.size = _
      rw [data.size,atEnd]
      change tree.nodes.data.size+1 = _
      omega
    have frame := default_frame tree (GeneralBorrowFreshMetadataChildDefault.result input) global output.2.1
      child parent parentNode newTag vacant present (GeneralBorrowFreshMetadataChildDefault.mapping input)
      (GeneralBorrowFreshMetadataChildDefault.locations input) (GeneralBorrowFreshMetadataChildDefault.shape input)
      (GeneralBorrowFreshMetadataChildDefault.exposure input) size data.roots
    refine ⟨child,data.freshLookup,frame,CurrentCallParentInsertion.of_leaf tree _ completion complete child parent frame primaryLive output.2.1.formed.toGraphState resultOrder,
      (fun ancestor path => CurrentCallResourceChild.ancestors_of_child tree completion complete child parent vacant path),?_⟩
    intro query node original
    exact old_default_of_stage tree (GeneralBorrowFreshMetadataChildDefault.result input) child parent parentNode newTag vacant present
      (GeneralBorrowFreshMetadataChildDefault.mapping input) (GeneralBorrowFreshMetadataChildDefault.locations input) (GeneralBorrowFreshMetadataChildDefault.shape input) query node original
  | reuse child available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildDefaultReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        child,available,bounded,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildDefaultReuse.reuse input
    have size : (GeneralBorrowFreshMetadataChildDefaultReuse.result input).nodes.data.size = max tree.nodes.data.size (child.toNat+1) := by
      change (GeneralBorrowFreshMetadataChildDefaultReuse.result input).nodes.size = _
      rw [data.size]
      change tree.nodes.data.size = _
      omega
    have frame := default_frame tree (GeneralBorrowFreshMetadataChildDefaultReuse.result input) global output.2.1
      child parent parentNode newTag vacant present (GeneralBorrowFreshMetadataChildDefaultReuse.mapping input)
      (GeneralBorrowFreshMetadataChildDefaultReuse.locations input) (GeneralBorrowFreshMetadataChildDefaultReuse.shape input)
      (GeneralBorrowFreshMetadataChildDefaultReuse.exposure input) size data.roots
    refine ⟨child,data.freshLookup,frame,CurrentCallParentInsertion.of_leaf tree _ completion complete child parent frame primaryLive output.2.1.formed.toGraphState resultOrder,
      (fun ancestor path => CurrentCallResourceChild.ancestors_of_child tree completion complete child parent vacant path),?_⟩
    intro query node original
    exact old_default_of_stage tree (GeneralBorrowFreshMetadataChildDefaultReuse.result input) child parent parentNode newTag vacant present
      (GeneralBorrowFreshMetadataChildDefaultReuse.mapping input) (GeneralBorrowFreshMetadataChildDefaultReuse.locations input) (GeneralBorrowFreshMetadataChildDefaultReuse.shape input) query node original

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

/-- A pure modifier's selected output window inherits any property proved from
its old prepared values. All splitting and selected-entry coverage are actual. -/
private theorem modify_owned (map : DedupRangeMap LocationTree) (offset len : Size)
    (well : map.WellFormed) (bounds : offset.bytes.toNat+len.bytes.toNat ≤ map.size.bytes.toNat)
    (modify : LocationTree → LocationTree) (idempotent : ∀ location, modify (modify location) = modify location)
    (P Q : LocationTree → Prop) (step : ∀ location, P location → Q (modify location))
    (owned : OwnedOn P offset.bytes (offset.bytes+len.bytes) map) :
    OwnedOn Q offset.bytes (offset.bytes+len.bytes)
      (map.modifyRange offset len (fun _ location => modify location)).state := by
  let prepared := map.iterMut offset len
  let changed := map.modifyRange offset len (fun _ location => modify location)
  have preparedGood := GeneralRangeMapOriginPrepare.iter_mut map offset len well bounds
  have preparedOwned := GeneralRangeMapOriginPrepare.selected_owned_on map offset len well bounds P
    offset.bytes (offset.bytes+len.bytes) owned (Nat.le_refl _) (Nat.le_refl _)
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
  obtain ⟨cursor,bounded,same⟩ := GeneralRangeMapCoverage.overlap_selected map offset len well bounds positive position oldValid start stop
  have member : position ∈ prepared.positions.toList := by
    rw [←same]
    exact Array.mem_def.mp (Array.mem_iff_getElem.mpr ⟨cursor,bounded,rfl⟩)
  simp only [show position ∈ (map.iterMut offset len).positions.toList from member,↓reduceIte] at entryEq
  rw [entryEq]
  apply step
  have segmentValid : cursor < prepared.segments.size := by rw [←preparedGood.1.lengths];exact bounded
  have selected := preparedOwned.2.2 cursor segmentValid
  have selectedEq := preparedGood.1.selected cursor bounded
  rw [selectedEq.2] at selected
  simpa only [same] using selected

open GeneralBorrowFreshGraph

private theorem stage_location (tree : BorrowTree) (completion : Completion) (held : ProtectedTags)
    (complete : ParentInterpretation tree completion) (child parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (vacant : tree.nodes.get child = none) (parentAt : tree.nodes.get parent = some parentNode)
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree) (location : LocationTree)
    (authority : Authority tree completion held parent location) :
    Authority (GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
      (GeneralBorrowFreshDefaultChild.child tag parent) mapping locations) (extend completion child parent) held child
      (GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshDefaultChild.inside) := by
  let stage := GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
    (GeneralBorrowFreshDefaultChild.child tag parent) mapping locations
  intro index node present
  by_cases new : index = child
  · subst index
    have raw : RawState (GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshDefaultChild.inside) child node =
        GeneralBorrowFreshDefaultChild.inside := by
      simp [RawState,GeneralBorrowFreshMaterialization.materialized,GeneralBorrowFreshLocation.get_same]
    constructor
    · intro _
      rw [raw]
      simp [LocalWrite,GeneralBorrowFreshDefaultChild.inside,LocationState.possible,Permission.isUnique]
    · intro outside
      exact False.elim (outside (.refl child))
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
    have effective : stateShape (RawState (GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshDefaultChild.inside) index node) =
        stateShape (RawState location index old) := by
      simp only [RawState,GeneralBorrowFreshMaterialization.materialized,
        GeneralBorrowFreshLocation.get_other _ _ _ _ new]
      cases location.perms.get index <;> simp [stateShape,TreeNode.defaultLocationState,defaultEq]
    have scalar := authority_state _ _ effective (held.contains node.tag)
    have original := authority index old oldAt
    rw [←tagEq] at original
    have ancestry := CurrentCallResourceChild.child_ancestry_iff tree completion complete child parent vacant ⟨parentNode,parentAt⟩ index
    constructor
    · intro below
      rcases ancestry.mp below with same | path
      · exact False.elim (new same)
      · exact scalar.1.mpr (original.1 path)
    · intro outside
      exact scalar.2.mpr (original.2 (fun below => outside (ancestry.mpr (.inr below))))

private theorem stage_owned (tree : BorrowTree) (completion : Completion) (held : ProtectedTags)
    (complete : ParentInterpretation tree completion) (child parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (vacant : tree.nodes.get child = none) (parentAt : tree.nodes.get parent = some parentNode)
    (mapping : UniKeyMap BorTag) (offset len : UInt64) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion held parent) offset (offset+len) tree.locations) :
    let locations := (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
      (fun _ location => GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshDefaultChild.inside)).state
    let stage := GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
      (GeneralBorrowFreshDefaultChild.child tag parent) mapping locations
    OwnedOn (Authority stage (extend completion child parent) held child) offset (offset+len) locations := by
  let locations := (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
    (fun _ location => GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshDefaultChild.inside)).state
  let stage := GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
    (GeneralBorrowFreshDefaultChild.child tag parent) mapping locations
  refine modify_owned tree.locations (Size.ofBytes offset) (Size.ofBytes len) well bounds
    (fun location => GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshDefaultChild.inside)
    (fun location => GeneralBorrowFreshInstallation.materialized_idempotent location child GeneralBorrowFreshDefaultChild.inside)
    (Authority tree completion held parent) (Authority stage (extend completion child parent) held child) ?_ owned
  intro location authority
  exact stage_location tree completion held complete child parent parentNode tag vacant parentAt mapping locations location authority

/-- Actual constructor transport. Only initial owned raw tables are supplied;
all post-constructor tables are derived for the actual allocator-chosen child.
The claim is confined to the requested window, where the new child is active. -/
private theorem construct (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : ParentInterpretation tree completion)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (unheld : global.protectedTags.contains newTag = false)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (primaryLive : ∃ node,tree.nodes.get allocationRoot=some node)
    (parentOrder : parentNode.tag.value≤newTag.value)
    (owned : OwnedOn (Authority tree completion global.protectedTags parent) offset (offset+len) tree.locations) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child, actual.tree.indexOfTag newTag = some child ∧
        ParentInterpretation actual.tree (extend completion child parent) ∧
        OwnedOn (Authority actual.tree (extend completion child parent) global.protectedTags child)
          offset (offset+len) actual.tree.locations ∧ LeafFrame tree actual.tree child parent ∧
        (∀ query node,tree.nodes.get query=some node →∃ next,actual.tree.nodes.get query=some next ∧
          next.defaultInitialPermission=node.defaultInitialPermission) := by
  obtain ⟨done,afterRuntime,capacity,growth,child,lookup,frame,completed,ancestry,defaults⟩ :=
    completion_construct tree global completion runtime complete parentTag newTag parent parentNode
      tagged present fresh room tagBound unheld offset len nonzero bounds primaryLive parentOrder
  refine ⟨done,afterRuntime,capacity,growth,child,lookup,completed,?_,frame,defaults⟩
  let rank := GeneralBorrowStructuralHistoryDefault.depth tree runtime.formed.toState
  let slot := GeneralBorrowStructuralHistoryDefault.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildDefault.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildDefault.append input
    have same : GeneralBorrowFreshMetadataChildDefault.index input = child := Option.some.inj (data.freshLookup.symm.trans lookup)
    have atEnd : (GeneralBorrowFreshMetadataChildDefault.index input).toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildDefault.at_end input
    have vacant : tree.nodes.get (GeneralBorrowFreshMetadataChildDefault.index input) = none := by
      simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _)]
    have staged := stage_owned tree completion global.protectedTags complete (GeneralBorrowFreshMetadataChildDefault.index input)
      parent parentNode newTag vacant present (GeneralBorrowFreshMetadataChildDefault.mapping input)
      offset len runtime.formed.well bounds owned
    have result := shape_owned (GeneralBorrowFreshMetadataChildDefault.stage input)
      (GeneralBorrowFreshMetadataChildDefault.result input) _ global.protectedTags (GeneralBorrowFreshMetadataChildDefault.index input)
      offset (offset+len) (GeneralBorrowFreshMetadataChildDefault.shape input) staged
    rw [same] at result
    simpa only [GeneralBorrowFreshMetadataChildDefault.result,input] using result
  | reuse index available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildDefaultReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        index,available,bounded,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildDefaultReuse.reuse input
    have same : index = child := Option.some.inj (data.freshLookup.symm.trans lookup)
    have staged := stage_owned tree completion global.protectedTags complete index parent parentNode newTag vacant present
      (GeneralBorrowFreshMetadataChildDefaultReuse.mapping input) offset len runtime.formed.well bounds owned
    have result := shape_owned (GeneralBorrowFreshMetadataChildDefaultReuse.stage input)
      (GeneralBorrowFreshMetadataChildDefaultReuse.result input) _ global.protectedTags index
      offset (offset+len) (GeneralBorrowFreshMetadataChildDefaultReuse.shape input) staged
    rw [same] at result
    simpa only [GeneralBorrowFreshMetadataChildDefaultReuse.result,input] using result


/-- The current optional-parent source drives one real Default mutable Read
and constructor. All operation outcomes are conclusions. -/
theorem prepare {before tracker data owner id offset length}
    (Q : CurrentCallResourceNormalization.UniformWindow before tracker data owner id offset length .mut)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra tracker.global)
    (tag : BorTag) (concrete : Q.pointer.value.provenance=.concrete id tag)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (distinct : Q.allocation.extra.roots.toList.Nodup) (short : Q.allocation.extra.nodes.size<65536)
    (nodeRoom : Q.allocation.extra.nodes.size+1≤4294967295)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount≠0) (bounds : start.toNat+amount.toNat≤Q.allocation.extra.locations.size.bytes.toNat) :
    let advanced:=GeneralBorrowFnEntryRegistration.advanced tracker.global room
    let accessed:=GeneralBorrowRawSharedExpression.read Q.allocation.extra tracker.global.protectedTags tag start amount .VisitChildrenOfAccessed
    let actual:=GeneralBorrowRawDefaultExpression.child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed
    accessed.status=.Completed ∧actual.outcome=.ok () ∧DuplicatePrefixBorrowContract.RuntimeFacts actual.tree advanced ∧
    actual.tree.locations.size=Q.allocation.extra.locations.size ∧actual.tree.nodes.size≤Q.allocation.extra.nodes.size+1 ∧
    ∃ index,actual.tree.indexOfTag tracker.global.nextPointerTag=some index ∧
      ParentInterpretation actual.tree (extend Q.precise.completion index Q.pointer.grant) ∧
      OwnedOn (Authority actual.tree (extend Q.precise.completion index Q.pointer.grant) advanced.protectedTags index)
        start (start+amount) actual.tree.locations ∧
      LeafFrame accessed.tree actual.tree index Q.pointer.grant ∧
      (∃ node,actual.tree.nodeAt index=some node ∧node.tag=tracker.global.nextPointerTag ∧node.isExposed=false) ∧
      ParentTagOrder actual.tree ∧GeneralBorrowFreshActiveWithin.ActiveWithin actual.tree index .Write start (start+amount) ∧
      (∀ target,GeneralBorrowFreshActiveWithin.ActiveWithin Q.allocation.extra target .Write start (start+amount) →
        GeneralBorrowFreshActiveWithin.ActiveWithin actual.tree target .Write start (start+amount)) ∧
      (∀ query node,Q.allocation.extra.nodes.get query=some node →∃ next,actual.tree.nodes.get query=some next ∧
        next.tag=node.tag ∧next.parent=node.parent ∧next.isExposed=node.isExposed ∧next.defaultInitialPermission=node.defaultInitialPermission) := by
  obtain ⟨P⟩:=CurrentCallResourceDefaultShared.prepare Q runtime tag concrete room distinct short start amount startEq amountEq bounds
  let advanced:=GeneralBorrowFnEntryRegistration.advanced tracker.global room
  let accessed:=GeneralBorrowRawSharedExpression.read Q.allocation.extra tracker.global.protectedTags tag start amount .VisitChildrenOfAccessed
  have high:=GeneralBorrowForestTagHighWater.complete Q.allocation.extra _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨fresh,_,unheld⟩:=GenericFunctionTagFormation.fresh_above Q.allocation.extra _ _ tracker.global.nextPointerTag high (Nat.le_refl _)
  obtain ⟨parent,parentAt,_,binding⟩:=Q.binding
  rw [concrete] at binding
  have present : accessed.tree.nodeAt Q.pointer.grant=some parent:=by change accessed.tree.nodes.get _=_;rw [P.nodes];exact parentAt
  have tagged : accessed.tree.indexOfTag tag=some Q.pointer.grant:=by rw [binding.2];exact P.runtime.formed.allocator.nodeTags _ _ present
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag:=by rw [P.tags];exact fresh
  have roomAfter : accessed.tree.nodes.size+1≤4294967295:=by change accessed.tree.nodes.data.size+1≤_;rw [P.nodes];exact nodeRoom
  have boundsAfter : start.toNat+amount.toNat≤accessed.tree.locations.size.bytes.toNat:=by rw [P.capacity];exact bounds
  have tagBound : tracker.global.nextPointerTag.value.toNat<advanced.nextPointerTag.value.toNat:=by
    have step:=GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  have primaryLive : ∃ node,accessed.tree.nodes.get allocationRoot=some node:=by
    obtain ⟨node,present,_,_,_⟩:=Q.issued.capability.rootNode
    exact ⟨node,by rw [P.nodes];exact present⟩
  have parentOrder : parent.tag.value≤tracker.global.nextPointerTag.value:=UInt64.le_of_lt
    (GeneralBorrowParentTagInvariant.parent_below_fresh Q.allocation.extra tracker.global runtime Q.pointer.grant parent parentAt)
  obtain ⟨done,afterRuntime,capacity,growth,index,lookup,parents,owned,frame,defaults⟩:=construct accessed.tree advanced Q.precise.completion
    P.runtime P.parents tag tracker.global.nextPointerTag Q.pointer.grant parent tagged present freshAfter roomAfter tagBound unheld
    start amount nonzero boundsAfter primaryLive parentOrder P.owned
  obtain ⟨metadataIndex,metadataLookup,metadataNode,_,_⟩:=GeneralBorrowDefaultChildMetadata.construct accessed.tree advanced P.runtime
    tag tracker.global.nextPointerTag Q.pointer.grant parent tagged present freshAfter roomAfter start amount nonzero boundsAfter
  have indexEq : metadataIndex=index:=Option.some.inj (metadataLookup.symm.trans lookup)
  subst metadataIndex
  obtain ⟨activeIndex,activeLookup,active⟩:=GeneralBorrowConstructorChildActivity.Default.construct accessed.tree advanced P.runtime
    tag tracker.global.nextPointerTag Q.pointer.grant parent tagged present freshAfter roomAfter start amount nonzero boundsAfter
  have activeEq : activeIndex=index:=Option.some.inj (activeLookup.symm.trans lookup)
  subst activeIndex
  have readOrder:=GeneralBorrowParentTagInvariant.nodes_frame Q.allocation.extra accessed.tree P.nodes Q.parents.order
  have order:=GeneralBorrowDefaultChildOrder.construct accessed.tree advanced P.runtime readOrder
    tag tracker.global.nextPointerTag Q.pointer.grant parent tagged present freshAfter roomAfter parentOrder start amount nonzero boundsAfter
  refine ⟨P.completed,done,afterRuntime,capacity.trans P.capacity,?_,index,lookup,parents,owned,frame,metadataNode,order,active,?_,?_⟩
  · calc _≤accessed.tree.nodes.size+1:=growth
         _=Q.allocation.extra.nodes.size+1:=congrArg (fun nodes : UniValMap TreeNode=>nodes.size+1) P.nodes
  · intro target active
    have readActive:=GeneralBorrowFreshActiveWithinAccess.normal Q.allocation.extra tag (Size.ofBytes start) (Size.ofBytes amount) .Read
      tracker.global.protectedTags .VisitChildrenOfAccessed target start (start+amount) runtime.formed.well bounds (Nat.le_refl _) (Nat.le_refl _) active
    exact GeneralBorrowRawTargetActivity.default_child accessed.tree advanced P.runtime tag tracker.global.nextPointerTag Q.pointer.grant parent
      tagged present freshAfter roomAfter start amount nonzero boundsAfter target start (start+amount) (Nat.le_refl _) (Nat.le_refl _) readActive
  · intro query node nodeAt
    have readAt : accessed.tree.nodes.get query=some node:=by rw [P.nodes];exact nodeAt
    obtain ⟨next,nextAt,nextTag,nextParent,nextExposed⟩:=frame.old query node readAt
    obtain ⟨other,otherAt,permission⟩:=defaults query node readAt
    have equal : other=next:=Option.some.inj (otherAt.symm.trans nextAt)
    exact ⟨next,nextAt,nextTag,nextParent,nextExposed,by rw [←equal];exact permission⟩

end
end DuplicatePrefix.CurrentCallResourceDefaultMutable
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceDefaultMutable" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved optional Default mutable dependency {dependency}"
