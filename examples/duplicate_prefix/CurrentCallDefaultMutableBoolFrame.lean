import duplicate_prefix.S05ConcreteProtectedChildAuthority
import duplicate_prefix.GeneralBorrowDefaultConstructorRuntime
import duplicate_prefix.GeneralBorrowDefaultChildMetadata
import duplicate_prefix.GeneralBorrowRawDefaultExpression
import duplicate_prefix.GeneralBorrowRangeOutsideOwned
import duplicate_prefix.CurrentCallReadRootActivity
import duplicate_prefix.CandidateCurrentJointRawReplacement
import duplicate_prefix.GeneralBorrowFnEntryRegistrationRuntime
import duplicate_prefix.GeneralBorrowFreshActiveWithin

/-! Same-allocation disjoint-window frame for the actual Default mutable
constructor. It preserves an old grant's raw authority; it does not restore an
entire Joint or require source/return allocation IDs to differ. -/
namespace DuplicatePrefix.CurrentCallDefaultMutableBoolFrame
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership OrdinaryBorrowAuthority
open GeneralBorrowView GeneralBorrowProjection GeneralRangeMapOrigins
open S05ConcreteProtectedChildCompletion
open S05CompletedAncestryReadMutable (Authority)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

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
    (complete : Completes tree completion) (child target : UniIndex)
    (vacant : tree.nodes.get child = none) (live : ∃ node, tree.nodes.get target = some node)
    (path : Below completion child target) : False := by
  induction path with
  | refl => obtain ⟨node,present⟩ := live; rw [vacant] at present; cases present
  | @step predecessor target edge path induction =>
    exact induction ((complete.2.2.2.2.2.2 target predecessor edge).2.1)

private theorem stage_location (tree : BorrowTree) (completion : Completion) (held : ProtectedTags)
    (complete : Completes tree completion) (child parent target : UniIndex) (parentNode targetNode : TreeNode) (tag : BorTag)
    (vacant : tree.nodes.get child = none) (parentAt : tree.nodes.get parent = some parentNode)
    (targetAt : tree.nodes.get target = some targetNode)
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree) (location : LocationTree)
    (clean : location.perms.get child = none)
    (authority : Authority tree completion held target location) :
    Authority (GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
      (GeneralBorrowFreshDefaultChild.child tag parent) mapping locations) (extend completion child parent) held target location := by
  intro index node present
  by_cases new : index = child
  · subst index
    dsimp only [GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,
      GeneralBorrowFreshNode.attachedNodes] at present
    have different : parent ≠ child := by intro same; rw [same,vacant] at parentAt; cases parentAt
    rw [GeneralBorrowFreshLocation.get_other _ _ _ _ (Ne.symm different),GeneralBorrowFreshLocation.get_same] at present
    have nodeEq : node = GeneralBorrowFreshDefaultChild.child tag parent := Option.some.inj present.symm
    have outside : ¬Below (extend completion child parent) child target := by
      intro path
      exact no_vacant_ancestor tree completion complete child target vacant ⟨targetNode,targetAt⟩
        ((old_ancestry_iff tree completion complete child parent vacant ⟨targetNode,targetAt⟩).mp path)
    constructor
    · intro impossible; exact False.elim (outside impossible)
    · intro _
      simp [RawState,clean,nodeEq,GeneralBorrowFreshDefaultChild.child,TreeNode.defaultLocationState,
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
    have ancestry := old_ancestry_iff tree completion complete child parent vacant ⟨targetNode,targetAt⟩ (ancestor := index)
    exact ⟨fun below => scalar.1.mpr (original.1 (ancestry.mp below)),
      fun outside => scalar.2.mpr (original.2 (fun below => outside (ancestry.mpr below)))⟩

private theorem stage_owned (tree : BorrowTree) (completion : Completion) (held : ProtectedTags)
    (complete : Completes tree completion) (child parent target : UniIndex) (parentNode targetNode : TreeNode) (tag : BorTag)
    (vacant : tree.nodes.get child = none) (parentAt : tree.nodes.get parent = some parentNode)
    (targetAt : tree.nodes.get target = some targetNode)
    (mapping : UniKeyMap BorTag) (offset len lower upper : UInt64) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (disjoint : ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
      point.toNat < offset.toNat ∨ (offset+len).toNat ≤ point.toNat)
    (clean : ∀ position (valid : position < tree.locations.entries.size), tree.locations.entries[position].data.perms.get child = none)
    (owned : OwnedOn (Authority tree completion held target) lower upper tree.locations) :
    let locations := (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
      (fun _ location => GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshDefaultChild.inside)).state
    let stage := GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
      (GeneralBorrowFreshDefaultChild.child tag parent) mapping locations
    OwnedOn (Authority stage (extend completion child parent) held target) lower upper locations := by
  let locations := (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
    (fun _ location => GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshDefaultChild.inside)).state
  have initial : OwnedOn (fun location => Authority tree completion held target location ∧ location.perms.get child = none)
      lower upper tree.locations := by
    intro position valid positive start stop
    exact ⟨owned position valid positive start stop,clean position valid⟩
  have unchanged := modify_outside_owned tree.locations (Size.ofBytes offset) (Size.ofBytes len) well bounds
    (fun location => GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshDefaultChild.inside)
    (fun location => GeneralBorrowFreshInstallation.materialized_idempotent location child GeneralBorrowFreshDefaultChild.inside)
    _ lower upper disjoint initial
  dsimp only
  intro position valid positive start stop
  obtain ⟨oldAuthority,oldClean⟩ := unchanged position valid positive start stop
  exact stage_location tree completion held complete child parent target parentNode targetNode tag vacant parentAt targetAt
    mapping locations _ oldClean oldAuthority

/-- Inserting another slot preserves the old anchor's activity at every byte.
The real range iterator may split segments; no unchanged-tree claim is used. -/
private theorem materialized_active (tree : BorrowTree) (child target : UniIndex)
    (different : target ≠ child) (offset len : Size) (kind : AccessKind) (lower upper : UInt64)
    (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree target kind lower upper) :
    GeneralBorrowFreshActiveWithin.Profile
      (tree.locations.modifyRange offset len (fun _ location =>
        GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshDefaultChild.inside)).state
      target kind lower upper := by
  let prepared := tree.locations.iterMut offset len
  let modify := fun (_ : ByteRange) location =>
    GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshDefaultChild.inside
  let updated := (tree.locations.modifyRange offset len modify).state
  have good := GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds
  have old := GeneralBorrowFreshActiveWithin.refines tree.locations prepared.state good.2.1 target kind lower upper active
  have sizes : updated.entries.size = prepared.state.entries.size := by
    dsimp only [updated,prepared]
    rw [GeneralBorrowFreshModify.state_exact tree.locations offset len modify well bounds,GeneralBorrowFreshModify.fold_size]
  intro point location valueAt state stored accessed accessKind associated
  obtain ⟨position,valid,start,stop,data⟩ := valueAt
  have oldValid : position < prepared.state.entries.size := by
    change position < updated.entries.size at valid
    omega
  obtain ⟨_,entry⟩ := GeneralBorrowFreshModify.entry_exact tree.locations offset len modify
    (fun _ location => GeneralBorrowFreshInstallation.materialized_idempotent location child GeneralBorrowFreshDefaultChild.inside)
    well bounds position oldValid
  change updated.entries[position] = _ at entry
  have range : updated.entries[position].range = prepared.state.entries[position].range := by
    have known := congrArg RangeMapSegment.range entry
    split at known <;> exact known
  change updated.entries[position].data = location at data
  have lookup : updated.entries[position].data.perms.get target = prepared.state.entries[position].data.perms.get target := by
    rw [entry]
    split
    · exact GeneralBorrowFreshLocation.get_other _ _ _ _ different
    · rfl
  rw [←data,lookup] at stored
  rw [range] at start stop
  exact old point prepared.state.entries[position].data ⟨position,oldValid,start,stop,rfl⟩ state stored accessed accessKind associated

private theorem old_node (tree after : BorrowTree) (child parent target : UniIndex)
    (parentNode targetNode : TreeNode) (newTag : BorTag) (mapping : UniKeyMap BorTag)
    (locations : DedupRangeMap LocationTree) (vacant : tree.nodes.get child = none)
    (targetAt : tree.nodes.get target = some targetNode) (different : target ≠ parent)
    (shape : treeShape after = treeShape (GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
      (GeneralBorrowFreshDefaultChild.child newTag parent) mapping locations))
    (exposure : GeneralBorrowFreshMetadataChildSifa.exposureShape after =
      GeneralBorrowFreshMetadataChildSifa.exposureShape (GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
        (GeneralBorrowFreshDefaultChild.child newTag parent) mapping locations)) :
    ∃ next, after.nodes.get target = some next ∧ next.tag = targetNode.tag ∧ next.parent = targetNode.parent ∧
      next.children = targetNode.children ∧ next.isExposed = targetNode.isExposed := by
  let stage := GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
    (GeneralBorrowFreshDefaultChild.child newTag parent) mapping locations
  have notChild : target ≠ child := by intro same; rw [same,vacant] at targetAt; cases targetAt
  have atStage : stage.nodes.get target = some targetNode := by
    dsimp only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes]
    rw [GeneralBorrowFreshLocation.get_other _ _ _ _ different,GeneralBorrowFreshLocation.get_other _ _ _ _ notChild]
    exact targetAt
  obtain ⟨next,found,tag,parentEq,children,_⟩ := GeneralBorrowFreshMetadata.node_fields stage after shape target targetNode atStage
  have flags := GeneralBorrowFreshMetadataChildSifa.lookup_exposure stage after exposure target
  rw [found,atStage] at flags
  exact ⟨next,found,tag,parentEq,children,by simpa only [Option.map_some,Option.some.injEq] using flags⟩

/-- The old target may inhabit the SAME allocation as the source window.
Only byte-window disjointness is required. The fresh Default child is a
foreign dormant reservation at these bytes, and old ancestry remains exact. -/
private theorem constructor (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion)
    (parentTag newTag : BorTag) (parent target : UniIndex) (parentNode targetNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (targetAt : tree.nodes.get target = some targetNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (aligned : global.protectedTags.contains newTag = false)
    (offset len lower upper : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (disjoint : ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
      point.toNat < offset.toNat ∨ (offset+len).toNat ≤ point.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags target) lower upper tree.locations) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child, actual.tree.indexOfTag newTag = some child ∧
        OwnedOn (Authority actual.tree (extend completion child parent) global.protectedTags target)
          lower upper actual.tree.locations := by
  obtain ⟨done,afterRuntime,capacity,growth⟩ := GeneralBorrowDefaultConstructorRuntime.construct
    tree global runtime parentTag newTag parent parentNode tagged present fresh room tagBound aligned offset len nonzero bounds
  obtain ⟨child,lookup,_,_,_⟩ := GeneralBorrowDefaultChildMetadata.construct
    tree global runtime parentTag newTag parent parentNode tagged present fresh room offset len nonzero bounds
  refine ⟨done,afterRuntime,capacity,growth,child,lookup,?_⟩
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
    have clean : ∀ position (valid : position < tree.locations.entries.size),
        tree.locations.entries[position].data.perms.get (GeneralBorrowFreshMetadataChildDefault.index input) = none := by
      intro position valid
      exact (runtime.formed.profile position valid).vacant _ vacant
    have staged := stage_owned tree completion global.protectedTags complete (GeneralBorrowFreshMetadataChildDefault.index input)
      parent target parentNode targetNode newTag vacant present targetAt (GeneralBorrowFreshMetadataChildDefault.mapping input)
      offset len lower upper runtime.formed.well bounds disjoint clean owned
    have result := shape_owned (GeneralBorrowFreshMetadataChildDefault.stage input)
      (GeneralBorrowFreshMetadataChildDefault.result input) _ global.protectedTags target
      lower upper (GeneralBorrowFreshMetadataChildDefault.shape input) staged
    rw [same] at result
    simpa only [GeneralBorrowFreshMetadataChildDefault.result,input] using result
  | reuse index available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildDefaultReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        index,available,bounded,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildDefaultReuse.reuse input
    have same : index = child := Option.some.inj (data.freshLookup.symm.trans lookup)
    have clean : ∀ position (valid : position < tree.locations.entries.size),
        tree.locations.entries[position].data.perms.get index = none := by
      intro position valid
      exact (runtime.formed.profile position valid).vacant _ vacant
    have staged := stage_owned tree completion global.protectedTags complete index parent target parentNode targetNode newTag vacant present targetAt
      (GeneralBorrowFreshMetadataChildDefaultReuse.mapping input) offset len lower upper runtime.formed.well bounds disjoint clean owned
    have result := shape_owned (GeneralBorrowFreshMetadataChildDefaultReuse.stage input)
      (GeneralBorrowFreshMetadataChildDefaultReuse.result input) _ global.protectedTags target
      lower upper (GeneralBorrowFreshMetadataChildDefaultReuse.shape input) staged
    rw [same] at result
    simpa only [GeneralBorrowFreshMetadataChildDefaultReuse.result,input] using result

/-- A distinct existing Bool child retains its exact leaf and exposure fields
and its bytewise activity through either actual Default allocator branch. -/
private theorem old_facets (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent target : UniIndex) (parentNode targetNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (targetAt : tree.nodes.get target = some targetNode) (different : target ≠ parent)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (kind : AccessKind) (lower upper : UInt64)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree target kind lower upper) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false
    (∃ next, actual.tree.nodes.get target = some next ∧ next.tag = targetNode.tag ∧ next.parent = targetNode.parent ∧
      next.children = targetNode.children ∧ next.isExposed = targetNode.isExposed) ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin actual.tree target kind lower upper := by
  let rank := GeneralBorrowStructuralHistoryDefault.depth tree runtime.formed.toState
  have slot := GeneralBorrowStructuralHistoryDefault.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildDefault.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
    let child := GeneralBorrowFreshMetadataChildDefault.index input
    have vacant : tree.nodes.get child = none := by
      have atEnd : child.toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildDefault.at_end input
      simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _)]
    have notChild : target ≠ child := by intro same; rw [same,vacant] at targetAt; cases targetAt
    have staged : GeneralBorrowFreshActiveWithin.ActiveWithin (GeneralBorrowFreshMetadataChildDefault.stage input) target kind lower upper :=
      materialized_active tree child target notChild (Size.ofBytes offset) (Size.ofBytes len) kind lower upper runtime.formed.well bounds active
    exact ⟨old_node tree _ child parent target parentNode targetNode newTag _ _ vacant targetAt different
      (GeneralBorrowFreshMetadataChildDefault.shape input) (GeneralBorrowFreshMetadataChildDefault.exposure input),
      GeneralBorrowFreshActiveWithin.shape_preserves _ _ (GeneralBorrowFreshMetadataChildDefault.shape input) target kind lower upper staged⟩
  | reuse child available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildDefaultReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        child,available,bounded,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
    have notChild : target ≠ child := by intro same; rw [same,vacant] at targetAt; cases targetAt
    have staged : GeneralBorrowFreshActiveWithin.ActiveWithin (GeneralBorrowFreshMetadataChildDefaultReuse.stage input) target kind lower upper :=
      materialized_active tree child target notChild (Size.ofBytes offset) (Size.ofBytes len) kind lower upper runtime.formed.well bounds active
    exact ⟨old_node tree _ child parent target parentNode targetNode newTag _ _ vacant targetAt different
      (GeneralBorrowFreshMetadataChildDefaultReuse.shape input) (GeneralBorrowFreshMetadataChildDefaultReuse.exposure input),
      GeneralBorrowFreshActiveWithin.shape_preserves _ _ (GeneralBorrowFreshMetadataChildDefaultReuse.shape input) target kind lower upper staged⟩

open GeneralBorrowRawDefaultExpression GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardParentTagOrder

/-- Default mutable-reference allocation, its actual associated Read, and its
actual unprotected reservation constructor preserve the current Bool child's disjoint authority
and exact hidden-leaf/activity facets. Both real allocator choices are covered. -/
theorem construct (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : Completes tree completion)
    (order : ParentTagOrder tree)
    (position : Nat) (selected parent target : UniIndex) (selectedNode parentNode targetNode : TreeNode)
    (slot : tree.roots[position]? = some selected) (selectedPresent : tree.nodes.get selected = some selectedNode)
    (parentPresent : tree.nodes.get parent = some parentNode) (parentPath : Path tree selected parent)
    (targetAt : tree.nodeAt target = some targetNode) (targetLeaf : targetNode.children = #[])
    (targetHidden : targetNode.isExposed = false) (different : target ≠ parent)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (nodeRoom : tree.nodes.size+1 ≤ 4294967295) (short : tree.nodes.size < 65536)
    (offset len lower upper : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (disjoint : ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
      point.toNat < offset.toNat ∨ (offset+len).toNat ≤ point.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags parent) offset (offset+len) tree.locations)
    (targetOwned : OwnedOn (Authority tree completion global.protectedTags target) lower upper tree.locations)
    (targetActive : GeneralBorrowFreshActiveWithin.ActiveWithin tree target .Write lower upper) :
    let advanced := GeneralBorrowFnEntryRegistration.advanced global room
    let accessed := read tree advanced.protectedTags parentNode.tag offset len .VisitChildrenOfAccessed
    let actual := child tree advanced.protectedTags parentNode.tag global.nextPointerTag offset len .VisitChildrenOfAccessed
    accessed.status = .Completed ∧ actual.outcome = .ok () ∧
    DuplicatePrefixBorrowContract.RuntimeFacts actual.tree advanced ∧ actual.tree.locations.size = tree.locations.size ∧
    actual.tree.nodes.size ≤ tree.nodes.size+1 ∧ ∃ freshChild,
      actual.tree.indexOfTag global.nextPointerTag = some freshChild ∧
      OwnedOn (Authority actual.tree (extend completion freshChild parent) advanced.protectedTags target) lower upper actual.tree.locations ∧
      (∃ next, actual.tree.nodeAt target = some next ∧ next.tag = targetNode.tag ∧ next.parent = targetNode.parent ∧
        next.children = targetNode.children ∧ next.isExposed = targetNode.isExposed) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin actual.tree target .Write lower upper := by
  let advanced := GeneralBorrowFnEntryRegistration.advanced global room
  have high := GeneralBorrowForestTagHighWater.complete tree _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨fresh,_,unheld⟩ := GenericFunctionTagFormation.fresh_above tree _ _ global.nextPointerTag high (Nat.le_refl _)
  obtain ⟨allocated,actual,below⟩ := GeneralBorrowForestTagHighWaterHistory.allocate tree global room runtime.below runtime.formed.allocator.nodeTags false
  have equal : advanced = allocated := congrArg Prod.fst
    (Except.ok.inj ((TypedRetagEmpty.allocate_tag global room).symm.trans actual))
  rw [←equal] at below
  have current : DuplicatePrefixBorrowContract.RuntimeFacts tree advanced :=
    ⟨runtime.formed,runtime.coherent,runtime.possible,by
      simpa only [GeneralBorrowFreshSharedSequence.registered,Bool.false_eq_true,ite_false,advanced,GeneralBorrowFnEntryRegistration.advanced] using below⟩
  obtain ⟨depth⟩ := current.formed.depth
  have rows : GeneralRangeMapOrigins.OwnedOn (fun location =>
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location ∧
      S05CompletedAncestryReadMutable.Authority tree completion advanced.protectedTags parent location)
      offset (offset+len) tree.locations := by
    intro cursor valid positive start stop
    exact ⟨current.possible cursor valid,owned cursor valid positive start stop⟩
  have accessed := S05CompletedAncestryReadMutable.range tree completion advanced.protectedTags complete
    current.formed.toGraphState depth order position selected parent selectedNode parentNode slot selectedPresent parentPresent parentPath
    (Size.ofBytes offset) (Size.ofBytes len) offset (offset+len) rows current.formed.well
    (fun cursor valid => ⟨current.coherent cursor valid,current.formed.profile cursor valid,current.possible cursor valid⟩)
    bounds (Nat.le_refl _) (Nat.le_refl _) short .VisitChildrenOfAccessed
  let after := read tree advanced.protectedTags parentNode.tag offset len .VisitChildrenOfAccessed
  have same : after.tree = {tree with locations := after.tree.locations} := accessed.tree_eq
  have afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts after.tree advanced := by
    rw [same]
    refine ⟨⟨⟨GeneralBorrowStructuralHistoryState.graph_locations tree _ current.formed.toGraphState,accessed.well⟩,?_⟩,
      ?_,?_,⟨current.below.mapping,current.below.protectors⟩⟩
    · intro cursor valid
      exact ⟨(accessed.runtime cursor valid).2.1.present,(accessed.runtime cursor valid).2.1.vacant⟩
    · intro cursor valid; exact (accessed.runtime cursor valid).1
    · intro cursor valid; exact (accessed.runtime cursor valid).2.2
  have tagged : after.tree.indexOfTag parentNode.tag = some parent := by
    unfold BorrowTree.indexOfTag
    change (tree.performBorrowAccessRange (.concrete parentNode.tag) (Size.ofBytes offset) (Size.ofBytes len) .Read advanced.protectedTags .VisitChildrenOfAccessed).tree.tagMapping.get parentNode.tag = _
    rw [accessed.tags]
    exact (complete.2.2.2.2.1 parent parentNode parentPresent).1
  have present : after.tree.nodeAt parent = some parentNode := by
    change after.tree.nodes.get parent = some parentNode
    simpa only [after,GeneralBorrowRawDefaultExpression.read,accessed.nodes] using parentPresent
  have freshAfter : GeneralBorrowTagMap.Fresh after.tree.tagMapping global.nextPointerTag := by
    simpa only [after,GeneralBorrowRawDefaultExpression.read,accessed.tags] using fresh
  have tagBound : global.nextPointerTag.value.toNat < advanced.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value global.nextPointerTag room
    change global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag global.nextPointerTag room).value.toNat
    omega
  have afterComplete : Completes after.tree completion := by
    rw [same]
    exact CandidateCurrentJointRawReplacement.completes tree completion _ complete
  have afterOwned : GeneralRangeMapOrigins.OwnedOn
      (S05CompletedAncestryReadMutable.Authority after.tree completion advanced.protectedTags parent)
      offset (offset+len) after.tree.locations := by
    intro cursor valid positive start stop index node nodeAt
    have authority := (accessed.rows cursor valid positive start stop).2
    exact authority index node (by simpa only [after,GeneralBorrowRawDefaultExpression.read,accessed.nodes] using nodeAt)
  have nodeRoomAfter : after.tree.nodes.size+1 ≤ 4294967295 := by
    simpa only [after,GeneralBorrowRawDefaultExpression.read,accessed.nodes] using nodeRoom
  have boundsAfter : offset.toNat+len.toNat ≤ after.tree.locations.size.bytes.toNat := by
    simpa only [after,GeneralBorrowRawDefaultExpression.read,accessed.capacity] using bounds
  have targetOwnedAfter : OwnedOn (Authority after.tree completion advanced.protectedTags target) lower upper after.tree.locations := by
    have retained := GeneralBorrowRangeOutsideOwned.owned (Authority tree completion advanced.protectedTags target)
      tree (.concrete parentNode.tag) (Size.ofBytes offset) (Size.ofBytes len) .Read advanced.protectedTags .VisitChildrenOfAccessed
      current.formed.well bounds lower upper disjoint targetOwned
    intro cursor valid positive start stop index node nodeAt
    exact retained cursor valid positive start stop index node (by simpa only [after,GeneralBorrowRawDefaultExpression.read,accessed.nodes] using nodeAt)
  have targetAfter : after.tree.nodeAt target = some targetNode := by
    simpa only [after,GeneralBorrowRawDefaultExpression.read,BorrowTree.nodeAt,accessed.nodes] using targetAt
  have readNormalRows : OwnedOn (fun location => Nonempty
      (DuplicatePrefixNormalKind.Capability tree location advanced.protectedTags parent .Read)) offset (offset+len) tree.locations := by
    intro cursor valid positive start stop
    have authority := owned cursor valid positive start stop
    obtain ⟨normal⟩ := S05CompletedAncestryNormal.normal tree completion _ advanced.protectedTags complete
      current.formed.toGraphState depth current.formed.fits position selected parent selectedNode slot selectedPresent parentPath
      (fun index node found _ => (authority index node found).1)
      (fun index node found _ => (authority index node found).2)
    exact ⟨DuplicatePrefixNormalKind.of_normal tree _ advanced.protectedTags parent normal .Read⟩
  have targetActiveAfter : GeneralBorrowFreshActiveWithin.ActiveWithin after.tree target .Write lower upper :=
    CurrentCallReadRootActivity.concrete_of_normal tree advanced current parentNode.tag parent target parentNode parentPresent
      offset len bounds readNormalRows ((complete.2.2.2.2.1 parent parentNode parentPresent).1)
      targetNode targetAt targetLeaf targetHidden different lower upper targetActive .VisitChildrenOfAccessed
  obtain ⟨done,resultRuntime,capacity,growth,freshChild,lookup,retained⟩ := constructor after.tree advanced completion
    afterRuntime afterComplete parentNode.tag global.nextPointerTag parent target parentNode targetNode tagged present targetAfter freshAfter nodeRoomAfter
    tagBound unheld offset len lower upper nonzero boundsAfter disjoint targetOwnedAfter
  have facets := old_facets after.tree advanced afterRuntime parentNode.tag global.nextPointerTag
    parent target parentNode targetNode tagged present targetAfter different freshAfter nodeRoomAfter offset len nonzero boundsAfter
    .Write lower upper targetActiveAfter
  refine ⟨accessed.completed,done,resultRuntime,capacity.trans accessed.capacity,?_,freshChild,lookup,retained,facets⟩
  simpa only [after,advanced,GeneralBorrowRawDefaultExpression.child,GeneralBorrowRawDefaultExpression.read,accessed.nodes] using growth

end DuplicatePrefix.CurrentCallDefaultMutableBoolFrame
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallDefaultMutableBoolFrame").length > 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved Default mutable Bool frame dependency {dependency}"
