import duplicate_prefix.CurrentCallSharedReference
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
namespace DuplicatePrefix.CurrentCallMutableReference
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Input Miri.Interpreter
open CandidateStableCallOwnership GeneralBorrowProjection OrdinaryBorrowAuthority
open S05ConcreteProtectedChildCompletion S05CompletedAncestryReadMutable
open CanonicalConfigFacts ActualReferenceContext
open GeneralBorrowRawDefaultExpression RootReferenceInfo RootReferenceTrees
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality
open GeneralRangeMapOrigins GeneralRangeMapState
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
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
private theorem completion_construct (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (unheld : global.protectedTags.contains newTag = false)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child, actual.tree.indexOfTag newTag = some child ∧
        S05ConcreteProtectedChildCompletion.LeafFrame tree actual.tree child parent ∧ Completes actual.tree (extend completion child parent) ∧
        (∀ ancestor, Below completion ancestor parent → Below (extend completion child parent) ancestor child) := by
  have output := GeneralBorrowDefaultConstructorRuntime.construct tree global runtime parentTag newTag parent parentNode
    tagged present fresh room tagBound unheld offset len nonzero bounds
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
    exact ⟨child,data.freshLookup,frame,completes_of_leaf tree _ completion complete child parent frame,
      fun ancestor path => ancestors_of_child tree completion complete child parent vacant path⟩
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
    exact ⟨child,data.freshLookup,frame,completes_of_leaf tree _ completion complete child parent frame,
      fun ancestor path => ancestors_of_child tree completion complete child parent vacant path⟩

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
    (complete : Completes tree completion) (child parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
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
    have ancestry := child_ancestry_iff tree completion complete child parent vacant ⟨parentNode,parentAt⟩ index
    constructor
    · intro below
      rcases ancestry.mp below with same | path
      · exact False.elim (new same)
      · exact scalar.1.mpr (original.1 path)
    · intro outside
      exact scalar.2.mpr (original.2 (fun below => outside (ancestry.mpr (.inr below))))

private theorem stage_owned (tree : BorrowTree) (completion : Completion) (held : ProtectedTags)
    (complete : Completes tree completion) (child parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
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
    (complete : Completes tree completion)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (unheld : global.protectedTags.contains newTag = false)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags parent) offset (offset+len) tree.locations) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child, actual.tree.indexOfTag newTag = some child ∧
        Completes actual.tree (extend completion child parent) ∧
        OwnedOn (Authority actual.tree (extend completion child parent) global.protectedTags child)
          offset (offset+len) actual.tree.locations ∧ LeafFrame tree actual.tree child parent := by
  obtain ⟨done,afterRuntime,capacity,growth,child,lookup,frame,completed,ancestry⟩ :=
    completion_construct tree global completion runtime complete parentTag newTag parent parentNode
      tagged present fresh room tagBound unheld offset len nonzero bounds
  refine ⟨done,afterRuntime,capacity,growth,child,lookup,completed,?_,frame⟩
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

private theorem prepare (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : Completes tree completion) (order : ParentTagOrder tree)
    (parent : UniIndex) (parentNode : TreeNode) (parentAt : tree.nodeAt parent = some parentNode)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (nodeRoom : tree.nodes.size+1 ≤ 4294967295) (short : tree.nodes.size < 65536)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags parent) offset (offset+len) tree.locations) :
    let advanced := GeneralBorrowFnEntryRegistration.advanced global room
    let read := GeneralBorrowRawDefaultExpression.read tree global.protectedTags parentNode.tag offset len .VisitChildrenOfAccessed
    let child := GeneralBorrowRawDefaultExpression.child tree global.protectedTags parentNode.tag global.nextPointerTag offset len .VisitChildrenOfAccessed
    read.status = .Completed ∧ child.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts child.tree advanced ∧
    child.tree.locations.size = tree.locations.size ∧ child.tree.nodes.size ≤ tree.nodes.size+1 ∧
    ∃ index, child.tree.indexOfTag global.nextPointerTag = some index ∧
      Completes child.tree (extend completion index parent) ∧
      OwnedOn (Authority child.tree (extend completion index parent) advanced.protectedTags index)
        offset (offset+len) child.tree.locations ∧
      LeafFrame read.tree child.tree index parent ∧
      (∃ node, child.tree.nodeAt index = some node ∧ node.tag = global.nextPointerTag ∧ node.isExposed = false) ∧ ParentTagOrder child.tree ∧
      (∀ target, GeneralBorrowFreshActiveWithin.ActiveWithin tree target .Write offset (offset+len) →
        GeneralBorrowFreshActiveWithin.ActiveWithin child.tree target .Write offset (offset+len)) ∧
      (∀ query node, tree.nodes.get query = some node →
        ∃ next, child.tree.nodes.get query = some next ∧ next.tag = node.tag ∧ next.parent = node.parent ∧ next.isExposed = node.isExposed) := by
  let advanced := GeneralBorrowFnEntryRegistration.advanced global room
  have high := GeneralBorrowForestTagHighWater.complete tree _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨fresh,_,unheld⟩ := GenericFunctionTagFormation.fresh_above tree _ _ global.nextPointerTag high (Nat.le_refl _)
  obtain ⟨allocated,actual,below⟩ := GeneralBorrowForestTagHighWaterHistory.allocate tree global room runtime.below runtime.formed.allocator.nodeTags false
  have equal : advanced = allocated := congrArg Prod.fst (Except.ok.inj ((TypedRetagEmpty.allocate_tag global room).symm.trans actual))
  rw [←equal] at below
  have current : DuplicatePrefixBorrowContract.RuntimeFacts tree advanced :=
    ⟨runtime.formed,runtime.coherent,runtime.possible,by
      simpa only [GeneralBorrowFreshSharedSequence.registered,Bool.false_eq_true,ite_false,advanced,GeneralBorrowFnEntryRegistration.advanced] using below⟩
  obtain ⟨depth⟩ := current.formed.depth
  obtain ⟨position,root,rootNode,slot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path tree current.formed.toGraphState parent parentNode parentAt
  have rows : OwnedOn (fun location => GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location ∧ Authority tree completion advanced.protectedTags parent location)
      offset (offset+len) tree.locations := by
    intro cursor valid positive start stop
    exact ⟨current.possible cursor valid,owned cursor valid positive start stop⟩
  have read := S05CompletedAncestryReadMutable.range tree completion advanced.protectedTags complete current.formed.toGraphState depth order
    position root parent rootNode parentNode slot rootAt parentAt path (Size.ofBytes offset) (Size.ofBytes len) offset (offset+len)
    rows current.formed.well (fun cursor valid => ⟨current.coherent cursor valid,current.formed.profile cursor valid,current.possible cursor valid⟩)
    bounds (Nat.le_refl _) (Nat.le_refl _) short .VisitChildrenOfAccessed
  let accessed := tree.performBorrowAccessRange (.concrete parentNode.tag) (Size.ofBytes offset) (Size.ofBytes len) .Read advanced.protectedTags .VisitChildrenOfAccessed
  have afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts accessed.tree advanced := by
    rw [read.tree_eq]
    refine ⟨⟨⟨GeneralBorrowStructuralHistoryState.graph_locations tree _ current.formed.toGraphState,read.well⟩,?_⟩,
      ?_,?_,⟨current.below.mapping,current.below.protectors⟩⟩
    · intro cursor valid
      exact ⟨(read.runtime cursor valid).2.1.present,(read.runtime cursor valid).2.1.vacant⟩
    · intro cursor valid;exact (read.runtime cursor valid).1
    · intro cursor valid;exact (read.runtime cursor valid).2.2
  have afterComplete : Completes accessed.tree completion := by
    rw [read.tree_eq]
    exact CandidateCurrentJointRawReplacement.completes tree completion _ complete
  have tagged : accessed.tree.indexOfTag parentNode.tag = some parent := by
    change accessed.tree.tagMapping.get parentNode.tag = some parent
    rw [read.tags]
    exact (complete.2.2.2.2.1 parent parentNode parentAt).1
  have present : accessed.tree.nodeAt parent = some parentNode := by change accessed.tree.nodes.get parent = _;rw [read.nodes];exact parentAt
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping global.nextPointerTag := by rw [read.tags];exact fresh
  have nodeRoomAfter : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [read.nodes];exact nodeRoom
  have boundsAfter : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [read.capacity];exact bounds
  have afterOwned : OwnedOn (Authority accessed.tree completion advanced.protectedTags parent) offset (offset+len) accessed.tree.locations := by
    have transport : ∀ location, Authority tree completion advanced.protectedTags parent location → Authority accessed.tree completion advanced.protectedTags parent location := by
      intro location old index node present
      rw [read.nodes] at present
      exact old index node present
    intro cursor valid positive start stop
    exact transport _ (read.rows cursor valid positive start stop).2
  have tagBound : global.nextPointerTag.value.toNat < advanced.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value global.nextPointerTag room
    change global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag global.nextPointerTag room).value.toNat
    omega
  obtain ⟨done,resultRuntime,capacity,growth,index,lookup,resultComplete,resultOwned,frame⟩ := construct accessed.tree advanced completion afterRuntime afterComplete
    parentNode.tag global.nextPointerTag parent parentNode tagged present freshAfter nodeRoomAfter tagBound unheld offset len nonzero boundsAfter afterOwned
  obtain ⟨metadataChild,metadataLookup,metadataNode,_,_⟩ := GeneralBorrowDefaultChildMetadata.construct accessed.tree advanced afterRuntime
    parentNode.tag global.nextPointerTag parent parentNode tagged present freshAfter nodeRoomAfter offset len nonzero boundsAfter
  have childEq : metadataChild = index := Option.some.inj (metadataLookup.symm.trans lookup)
  rw [childEq] at metadataNode
  have readOrder := GeneralBorrowParentTagInvariant.nodes_frame tree accessed.tree read.nodes order
  have older := GeneralBorrowParentTagInvariant.parent_below_fresh tree global runtime parent parentNode parentAt
  have resultOrder := GeneralBorrowDefaultChildOrder.construct accessed.tree advanced afterRuntime readOrder
    parentNode.tag global.nextPointerTag parent parentNode tagged present freshAfter nodeRoomAfter
    (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp older))) offset len nonzero boundsAfter
  refine ⟨read.completed,done,resultRuntime,capacity.trans read.capacity,?_,index,lookup,resultComplete,resultOwned,frame,metadataNode,resultOrder,?_,?_⟩
  · calc _ ≤ accessed.tree.nodes.size+1 := growth
         _ = tree.nodes.size+1 := congrArg (fun value : UniValMap TreeNode => value.size+1) read.nodes
  · intro target active
    have afterActive := GeneralBorrowFreshActiveWithinAccess.normal tree parentNode.tag (Size.ofBytes offset) (Size.ofBytes len) .Read
      advanced.protectedTags .VisitChildrenOfAccessed target offset (offset+len) runtime.formed.well bounds (Nat.le_refl _) (Nat.le_refl _) active
    exact GeneralBorrowRawTargetActivity.default_child accessed.tree advanced afterRuntime parentNode.tag global.nextPointerTag parent parentNode
      tagged present freshAfter nodeRoomAfter offset len nonzero boundsAfter target offset (offset+len) (Nat.le_refl _) (Nat.le_refl _) afterActive
  · intro query node nodeAt
    exact frame.old query node (by change accessed.tree.nodes.get query = _;rw [read.nodes];exact nodeAt)

private theorem rvalue_of_steps
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator) (region : Region)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = validityFuel+1)
    (base offset len : UInt64)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (_defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (parentTag : BorTag)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (readCompleted : (GeneralBorrowRawDefaultExpression.read entry.allocation.extra tracker.global.protectedTags parentTag offset len .VisitChildrenOfAccessed).status = .Completed)
    (childCompleted : (GeneralBorrowRawDefaultExpression.child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).outcome = .ok ())
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (localId : MIR.LocalId) (different : localId ≠ 1)
    (validSource : (1 : MIR.LocalId) < frame.locals.size) (validDest : localId < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (destLive : frame.locals[localId].value = .live (.immediate .uninit))
    (destUncached : frame.locals[localId].layout = none)
    (query : CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler localId
      (Storage.withCurrent frames frame machine) = .ok (layout false) (Storage.withCurrent frames frame machine))
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine))) :
    let inner := config options remaining span
    let value := RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (layout false)
    let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
      memory := RetagEntry.updatedMemory machine.memory id entry (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree}
    evalRvalueIntoPlace (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.Ref region (RootReferenceRvalue.borrowKind false) ⟨1,#[.Deref]⟩) ⟨localId,#[]⟩ (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (ActualLocalCopy.written frame localId (layout false) validDest value.imm) resultMachine) := by
  have notConstructed := DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ metadata cacheOrigins
  let inner := config options remaining span
  let outer := PreparedContracts.actualConfig options () (remaining+1) span
  let hooks := ExecutionMachine.rvalueHooks outer limits
  let cachedFrame := LocalPlaces.cachePlaceLayout frame localId (layout false) validDest
  let activeTracker := {tracker with retagMode := mode false}
  let enteredMachine := RootReferenceRvalue.enter machine tracker false
  let updatedMachine := {ReferenceBorrowDriver.allocatedMachine enteredMachine activeTracker fresh with
    memory := RetagEntry.updatedMemory machine.memory id entry (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree}
  let value := RetagReferencePlace.sliceValue inner.access.runtime.base
    (Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (layout false)
  let afterFrame := RootReferenceWrite.written cachedFrame localId value.imm
    (by simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validDest)
  have info := RootReferenceInfo.facts options remaining span ctx false
  have destination := ActualLocalPlace.uncached options limits (remaining+1) span debugOff frames frame machine
    localId (layout false) validDest destUncached info.sized query
  have cachedSourceValid : (1 : MIR.LocalId) < cachedFrame.locals.size := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validSource
  have cachedDestValid : localId < cachedFrame.locals.size := by simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validDest
  have sourceLive' : cachedFrame.locals[1].value = .live (.immediate
      (PtrMetadataComplete.rawImmediate (.inl (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))) outer.access.runtime.base len)) := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set,different,PtrMetadataComplete.rawImmediate,RetagReferencePlace.sliceValue,outer] using sourceLive
  have sourceCached' : cachedFrame.locals[1].layout = some ActualReferenceMetadata.reference := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set,different] using sourceCached
  have sourcePlace := RootReferencePlace.actual_slice_place options limits (remaining+1) span debugOff frames cachedFrame machine
    1 (.inl (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))) len cachedSourceValid sourceLive' sourceCached' noClocks ghost
  have destinationLive : cachedFrame.locals[localId].value = .live (.immediate .uninit) := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using destLive
  have destinationCached : cachedFrame.locals[localId].layout = some (layout false) := by
    simp [cachedFrame,LocalPlaces.cachePlaceLayout]
  have entered : enteredMachine.borrowTracker = some activeTracker := rfl
  have current : activeTracker.retagMode = mode false := rfl
  have run := And.intro readCompleted childCompleted
  let parentTree := (read entry.allocation.extra tracker.global.protectedTags parentTag offset len .VisitChildrenOfAccessed).tree
  let resultTree := (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree
  have readTree : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset)
      (Size.ofBytes len) .Read activeTracker.global.protectedTags .VisitChildrenOfAccessed).tree = parentTree := rfl
  have readDone : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset)
      (Size.ofBytes len) .Read activeTracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed := run.1
  have child' : parentTree.newChild (Size.ofBytes offset) (.concrete parentTag) activeTracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) (initial false)) (policy false).outsidePermission false =
      ⟨resultTree,.ok ()⟩ := by
    have succeeded := run.2
    change (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).outcome = .ok () at succeeded
    change child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed =
      ⟨(child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree,.ok ()⟩
    cases childEq : child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed with
    | mk treeResult result =>
      simp only [childEq] at succeeded
      cases succeeded
      rfl
  have physicalBounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat := by
    rw [←capacity]
    exact bounds
  have writer := RootReferenceWrite.positive_cached options limits remaining span ctx debugOff cmp false dynamicFuel validityFuel
    fuelEq validationFuel id entry base offset len parentTag positive nonzero signedFits physicalBounds
    frames cachedFrame enteredMachine activeTracker entered current fresh localId .uninit cachedDestValid destinationLive destinationCached
    noClocks ghost shallow cachedAddress present race parentTree (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree
    readTree readDone child' metadata notConstructed
  have baseEq : outer.access.runtime.base = inner.access.runtime.base := by
    rw [CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span,
      CanonicalConfigFacts.actual_access_runtime options () remaining span]
  have writer' : hooks.writeImmediate ()
      (PtrMetadataComplete.rawImmediate (.inl (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))) outer.access.runtime.base len)
      (LocalPlaces.localRuntimePlace frames.size cachedFrame localId (layout false))
      (Storage.withCurrent frames cachedFrame enteredMachine) = .ok () (Storage.withCurrent frames afterFrame updatedMachine) := by
    simpa only [hooks,outer,inner,afterFrame,value,activeTracker,baseEq,PtrMetadataComplete.rawImmediate,RetagReferencePlace.sliceValue,updatedMachine,enteredMachine,RootReferenceRvalue.enter] using writer
  have result := RootReferenceRvalue.of_write options limits (remaining+1) span false region
    (.inl (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))) len ⟨1,#[.Deref]⟩ ⟨localId,#[]⟩
    (LocalPlaces.localRuntimePlace frames.size cachedFrame localId (layout false)) (Storage.withCurrent frames frame machine)
    frames cachedFrame machine tracker (ReferenceBorrowDriver.allocatedTracker activeTracker fresh) enabled shallow rfl
    destination sourcePlace afterFrame updatedMachine rfl writer'
  simpa only [afterFrame,updatedMachine,enteredMachine,RootReferenceRvalue.enter,ReferenceBorrowDriver.allocatedMachine,
    ReferenceBorrowDriver.allocatedTracker,activeTracker,RootReferenceWrite.written,ActualLocalCopy.written,cachedFrame,value,
    inner] using result

private theorem statement_of_steps
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = validityFuel+1)
    (base offset len : UInt64)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir (RootReferenceFacts.location false))
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (parentTag : BorTag)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (readCompleted : (GeneralBorrowRawDefaultExpression.read entry.allocation.extra tracker.global.protectedTags parentTag offset len .VisitChildrenOfAccessed).status = .Completed)
    (childCompleted : (GeneralBorrowRawDefaultExpression.child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).outcome = .ok ())
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (validSource : (1 : MIR.LocalId) < frame.locals.size) (validDest : (RootReferenceFacts.destination false) < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (destLive : frame.locals[RootReferenceFacts.destination false].value = .live (.immediate .uninit))
    (destUncached : frame.locals[RootReferenceFacts.destination false].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine))) :
    let inner := config options remaining span
    let value := RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (layout false)
    let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
      memory := RetagEntry.updatedMemory machine.memory id entry (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree}
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent frames frame machine) =
      (Storage.withCurrent frames (CopyHelperSteps.advance
        (ActualLocalCopy.written frame (RootReferenceFacts.destination false) (layout false) validDest value.imm)
        (RootReferenceFacts.location false)) resultMachine,.ok true) := by
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span preciseOff implicitOff
  have query := RootReferenceFacts.compute_destination frames frame machine sourceBody identity callee false
  have different : RootReferenceFacts.destination false ≠ 1 := by decide
  have rvalue := rvalue_of_steps options limits remaining span ctx debugOff cmp .Erased dynamicFuel validityFuel fuelEq validationFuel
    base offset len id entry positive nonzero signedFits frames frame machine tracker enabled
    defaultMode fresh parentTag bounds readCompleted childCompleted capacity (RootReferenceFacts.destination false) different validSource validDest sourceLive sourceCached
    destLive destUncached query noClocks ghost shallow cachedAddress present race metadata cacheOrigins
  let inner := config options remaining span
  let value := RetagReferencePlace.sliceValue inner.access.runtime.base
    (Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (layout false)
  let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
    memory := RetagEntry.updatedMemory machine.memory id entry (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree}
  let resultFrame := ActualLocalCopy.written frame (RootReferenceFacts.destination false) (layout false) validDest value.imm
  apply CopyHelperSteps.assign_of_actual_rvalue (PreparedContracts.actualConfig options () (remaining+1) span) limits
    frames frame resultFrame machine resultMachine (RootReferenceFacts.location false)
    ⟨RootReferenceFacts.destination false,#[]⟩ (.Ref .Erased (RootReferenceRvalue.borrowKind false) ⟨1,#[.Deref]⟩) located
  · simpa [resultFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using located
  · rw [sourceBody]
    exact RootReferenceFacts.statement false
  · exact rvalue

theorem statement
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = validityFuel+1)
    (base offset len : UInt64)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir (RootReferenceFacts.location false))
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (parentTag : BorTag)
    (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (complete : Completes entry.allocation.extra completion) (order : ParentTagOrder entry.allocation.extra)
    (parent : UniIndex) (parentNode : TreeNode) (parentAt : entry.allocation.extra.nodeAt parent = some parentNode)
    (parentTagEq : parentNode.tag = parentTag)
    (nodeRoom : entry.allocation.extra.nodes.size+1 ≤ 4294967295) (short : entry.allocation.extra.nodes.size < 65536)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority entry.allocation.extra completion tracker.global.protectedTags parent)
      offset (offset+len) entry.allocation.extra.locations)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (validSource : (1 : MIR.LocalId) < frame.locals.size) (validDest : (RootReferenceFacts.destination false) < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (destLive : frame.locals[RootReferenceFacts.destination false].value = .live (.immediate .uninit))
    (destUncached : frame.locals[RootReferenceFacts.destination false].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine))) :
    let inner := config options remaining span
    let value := RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (layout false)
    let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
      memory := RetagEntry.updatedMemory machine.memory id entry (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree}
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent frames frame machine) =
      (Storage.withCurrent frames (CopyHelperSteps.advance
        (ActualLocalCopy.written frame (RootReferenceFacts.destination false) (layout false) validDest value.imm)
        (RootReferenceFacts.location false)) resultMachine,.ok true) ∧
    let resultTree := (GeneralBorrowRawDefaultExpression.child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree
    DuplicatePrefixBorrowContract.RuntimeFacts resultTree (ReferenceBorrowDriver.allocatedTracker tracker fresh).global ∧
    resultTree.locations.size = entry.allocation.extra.locations.size ∧ resultTree.nodes.size ≤ entry.allocation.extra.nodes.size+1 ∧
    ∃ child, resultTree.indexOfTag tracker.global.nextPointerTag = some child ∧
      Completes resultTree (extend completion child parent) ∧
      OwnedOn (Authority resultTree (extend completion child parent) (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.protectedTags child)
        offset (offset+len) resultTree.locations ∧
      (∃ node, resultTree.nodeAt child = some node ∧ node.tag = tracker.global.nextPointerTag ∧ node.isExposed = false) ∧ ParentTagOrder resultTree ∧
      (∀ target, GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra target .Write offset (offset+len) →
        GeneralBorrowFreshActiveWithin.ActiveWithin resultTree target .Write offset (offset+len)) ∧
      (∀ query node, entry.allocation.extra.nodes.get query = some node →
        ∃ next, resultTree.nodes.get query = some next ∧ next.tag = node.tag ∧ next.parent = node.parent ∧ next.isExposed = node.isExposed) := by
  have nonzeroLen : len ≠ 0 := by intro zero;subst len;exact (by decide : ¬((0 : UInt64)<0)) positive
  have run := prepare entry.allocation.extra tracker.global completion runtime complete order parent parentNode parentAt fresh nodeRoom short
    offset len nonzeroLen bounds owned
  rw [parentTagEq] at run
  have actual := statement_of_steps options limits remaining span preciseOff implicitOff debugOff cmp dynamicFuel validityFuel fuelEq validationFuel
    base offset len id entry positive nonzero signedFits frames frame machine sourceBody identity callee located tracker enabled defaultMode fresh parentTag
    bounds run.1 run.2.1 capacity validSource validDest sourceLive sourceCached destLive destUncached noClocks ghost shallow cachedAddress present race metadata cacheOrigins
  exact ⟨actual,run.2.2.1,run.2.2.2.1,run.2.2.2.2.1,by
    obtain ⟨child,lookup,completed,authority,_,node,ordered,activity,oldNodes⟩ := run.2.2.2.2.2
    exact ⟨child,lookup,completed,authority,node,ordered,activity,oldNodes⟩⟩

end
end DuplicatePrefix.CurrentCallMutableReference
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallMutableReference.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current mutable-reference dependency {dependency}"
