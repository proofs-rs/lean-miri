import duplicate_prefix.S05ConcreteProtectedChildCompletion
import duplicate_prefix.S05CompletedAncestryReadMutable
import duplicate_prefix.GeneralBorrowFreshInstallation
import duplicate_prefix.GeneralBorrowSharedConstructorRuntime
import duplicate_prefix.GeneralBorrowSharedChildGraph

/-! Unprotected Frozen construction retains the old parent's mutable authority.
This concerns the actual constructor window and finite completion, not admission. -/
namespace DuplicatePrefix.S05DefaultSharedAuthority
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
open GeneralBorrowFreshAnchor (sharedNode sharedState)

private theorem ancestor_live (tree : BorrowTree) (completion : Completion)
    (complete : Completes tree completion) {ancestor target : UniIndex}
    (path : Below completion ancestor target) (targetLive : ∃ node, tree.nodes.get target = some node) :
    ∃ node, tree.nodes.get ancestor = some node := by
  induction path with
  | refl => exact targetLive
  | @step predecessor target edge path induction =>
    exact induction (complete.2.2.2.2.2.2 target predecessor edge).2.1

private theorem stage_location (tree : BorrowTree) (completion : Completion) (held : ProtectedTags)
    (complete : Completes tree completion) (child parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (vacant : tree.nodes.get child = none) (parentAt : tree.nodes.get parent = some parentNode)
    (unheld : held.contains tag = false)
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree) (location : LocationTree)
    (authority : Authority tree completion held parent location) :
    Authority (GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
      (sharedNode tag parent) mapping locations) (extend completion child parent) held parent
      (GeneralBorrowFreshMaterialization.materialized location child sharedState) := by
  let stage := GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
    (sharedNode tag parent) mapping locations
  intro index node present
  by_cases new : index = child
  · subst index
    have different : parent ≠ child := by intro same;rw [same,vacant] at parentAt;cases parentAt
    have childAt : stage.nodes.get child = some (sharedNode tag parent) := by
      dsimp only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,
        GeneralBorrowFreshNode.attachedNodes]
      rw [GeneralBorrowFreshLocation.get_other _ _ _ _ (Ne.symm different),GeneralBorrowFreshLocation.get_same]
    have nodeEq : node = sharedNode tag parent := Option.some.inj (present.symm.trans childAt)
    have raw : RawState (GeneralBorrowFreshMaterialization.materialized location child sharedState) child node = sharedState := by
      simp [RawState,GeneralBorrowFreshMaterialization.materialized,GeneralBorrowFreshLocation.get_same]
    constructor
    · intro below
      have old := (old_ancestry_iff tree completion complete child parent vacant ⟨parentNode,parentAt⟩).mp below
      obtain ⟨oldNode,oldAt⟩ := ancestor_live tree completion complete old ⟨parentNode,parentAt⟩
      rw [vacant] at oldAt
      cases oldAt
    · intro _
      rw [raw,nodeEq]
      simp [ForeignWrite,sharedState,sharedNode,unheld,LocationState.possible]
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
    have effective : stateShape (RawState (GeneralBorrowFreshMaterialization.materialized location child sharedState) index node) =
        stateShape (RawState location index old) := by
      simp only [RawState,GeneralBorrowFreshMaterialization.materialized,GeneralBorrowFreshLocation.get_other _ _ _ _ new]
      cases location.perms.get index <;> simp [stateShape,TreeNode.defaultLocationState,defaultEq]
    have scalar := authority_state _ _ effective (held.contains node.tag)
    have original := authority index old oldAt
    rw [←tagEq] at original
    have ancestry := old_ancestry_iff tree completion complete child parent vacant (ancestor := index) ⟨parentNode,parentAt⟩
    exact ⟨fun below => scalar.1.mpr (original.1 (ancestry.mp below)),
      fun outside => scalar.2.mpr (original.2 (fun below => outside (ancestry.mpr below)))⟩

private theorem stage_owned (tree : BorrowTree) (completion : Completion) (held : ProtectedTags)
    (complete : Completes tree completion) (child parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (vacant : tree.nodes.get child = none) (parentAt : tree.nodes.get parent = some parentNode)
    (unheld : held.contains tag = false) (mapping : UniKeyMap BorTag)
    (offset len : UInt64) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion held parent) offset (offset+len) tree.locations) :
    let locations := (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
      (fun _ location => GeneralBorrowFreshMaterialization.materialized location child sharedState)).state
    let stage := GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
      (sharedNode tag parent) mapping locations
    OwnedOn (Authority stage (extend completion child parent) held parent) offset (offset+len) locations := by
  let locations := (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
    (fun _ location => GeneralBorrowFreshMaterialization.materialized location child sharedState)).state
  let stage := GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
    (sharedNode tag parent) mapping locations
  refine modify_owned tree.locations (Size.ofBytes offset) (Size.ofBytes len) well bounds
    (fun location => GeneralBorrowFreshMaterialization.materialized location child sharedState)
    (fun location => GeneralBorrowFreshInstallation.materialized_idempotent location child sharedState)
    (Authority tree completion held parent) (Authority stage (extend completion child parent) held parent) ?_ owned
  intro location authority
  exact stage_location tree completion held complete child parent parentNode tag vacant parentAt unheld mapping locations location authority

theorem construct (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : Completes tree completion)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (unheld : global.protectedTags.contains newTag = false)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags parent) offset (offset+len) tree.locations) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) sharedState) .Frozen false
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child, actual.tree.indexOfTag newTag = some child ∧
        OwnedOn (Authority actual.tree (extend completion child parent) global.protectedTags parent)
          offset (offset+len) actual.tree.locations := by
  obtain ⟨done,afterRuntime,capacity,growth⟩ := GeneralBorrowSharedConstructorRuntime.construct
    tree global runtime parentTag newTag parent parentNode tagged present fresh room tagBound false unheld offset len nonzero bounds
  obtain ⟨child,lookup,_,_⟩ := GeneralBorrowSharedChildGraph.construct
    tree global runtime parentTag newTag parent parentNode tagged present fresh room false offset len nonzero bounds
  refine ⟨done,afterRuntime,capacity,growth,child,lookup,?_⟩
  let rank := GeneralBorrowStructuralHistoryShared.depth tree runtime.formed.toState
  let slot := GeneralBorrowStructuralHistoryShared.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,false,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildShared.append input
    have same : GeneralBorrowFreshMetadataChildShared.index input = child := Option.some.inj (data.freshLookup.symm.trans lookup)
    have atEnd : (GeneralBorrowFreshMetadataChildShared.index input).toNat = tree.nodes.data.size :=
      GeneralBorrowFreshMetadataChildShared.at_end input
    have vacant : tree.nodes.get (GeneralBorrowFreshMetadataChildShared.index input) = none := by
      simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _)]
    have staged := stage_owned tree completion global.protectedTags complete _ parent parentNode newTag vacant present unheld
      (GeneralBorrowFreshMetadataChildShared.mapping input) offset len runtime.formed.well bounds owned
    have result := shape_owned (GeneralBorrowFreshMetadataChildShared.stage input)
      (GeneralBorrowFreshMetadataChildShared.result input) _ global.protectedTags parent offset (offset+len)
      (GeneralBorrowFreshMetadataChildShared.shape input) staged
    rw [same] at result
    simpa only [GeneralBorrowFreshMetadataChildShared.result,input] using result
  | reuse index available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        index,available,bounded,vacant,slack,false,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildSharedReuse.reuse input
    have same : index = child := Option.some.inj (data.freshLookup.symm.trans lookup)
    have staged := stage_owned tree completion global.protectedTags complete index parent parentNode newTag vacant present unheld
      (GeneralBorrowFreshMetadataChildSharedReuse.mapping input) offset len runtime.formed.well bounds owned
    have result := shape_owned (GeneralBorrowFreshMetadataChildSharedReuse.stage input)
      (GeneralBorrowFreshMetadataChildSharedReuse.result input) _ global.protectedTags parent offset (offset+len)
      (GeneralBorrowFreshMetadataChildSharedReuse.shape input) staged
    rw [same] at result
    simpa only [GeneralBorrowFreshMetadataChildSharedReuse.result,input] using result

end DuplicatePrefix.S05DefaultSharedAuthority
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05DefaultSharedAuthority." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved default shared authority dependency {dependency}"
