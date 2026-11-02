import duplicate_prefix.S05ConcreteProtectedChildAuthority

/-! Same-allocation disjoint-window frame for the actual protected concrete
constructor. It preserves an old grant's raw authority; it does not restore an
entire Joint or require source/return allocation IDs to differ. -/
namespace DuplicatePrefix.S05ConcreteProtectedChildDisjoint
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
      (GeneralBorrowFreshChild.child tag parent) mapping locations) (extend completion child parent) held target location := by
  intro index node present
  by_cases new : index = child
  · subst index
    dsimp only [GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,
      GeneralBorrowFreshNode.attachedNodes] at present
    have different : parent ≠ child := by intro same; rw [same,vacant] at parentAt; cases parentAt
    rw [GeneralBorrowFreshLocation.get_other _ _ _ _ (Ne.symm different),GeneralBorrowFreshLocation.get_same] at present
    have nodeEq : node = GeneralBorrowFreshChild.child tag parent := Option.some.inj present.symm
    have outside : ¬Below (extend completion child parent) child target := by
      intro path
      exact no_vacant_ancestor tree completion complete child target vacant ⟨targetNode,targetAt⟩
        ((old_ancestry_iff tree completion complete child parent vacant ⟨targetNode,targetAt⟩).mp path)
    constructor
    · intro impossible; exact False.elim (outside impossible)
    · intro _
      simp [RawState,clean,nodeEq,GeneralBorrowFreshChild.child,TreeNode.defaultLocationState,
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
      (fun _ location => GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshChild.inside)).state
    let stage := GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
      (GeneralBorrowFreshChild.child tag parent) mapping locations
    OwnedOn (Authority stage (extend completion child parent) held target) lower upper locations := by
  let locations := (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
    (fun _ location => GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshChild.inside)).state
  have initial : OwnedOn (fun location => Authority tree completion held target location ∧ location.perms.get child = none)
      lower upper tree.locations := by
    intro position valid positive start stop
    exact ⟨owned position valid positive start stop,clean position valid⟩
  have unchanged := modify_outside_owned tree.locations (Size.ofBytes offset) (Size.ofBytes len) well bounds
    (fun location => GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshChild.inside)
    (fun location => GeneralBorrowFreshInstallation.materialized_idempotent location child GeneralBorrowFreshChild.inside)
    _ lower upper disjoint initial
  dsimp only
  intro position valid positive start stop
  obtain ⟨oldAuthority,oldClean⟩ := unchanged position valid positive start stop
  exact stage_location tree completion held complete child parent target parentNode targetNode tag vacant parentAt targetAt
    mapping locations _ oldClean oldAuthority

/-- The old target may inhabit the SAME allocation as the source window.
Only byte-window disjointness is required. The fresh protected child is a
foreign dormant reservation at these bytes, and old ancestry remains exact. -/
theorem construct (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion)
    (parentTag newTag : BorTag) (parent target : UniIndex) (parentNode targetNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (targetAt : tree.nodes.get target = some targetNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (held : global.protectedTags.contains newTag = true)
    (offset len lower upper : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (disjoint : ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
      point.toNat < offset.toNat ∨ (offset+len).toNat ≤ point.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags target) lower upper tree.locations) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child, actual.tree.indexOfTag newTag = some child ∧
        Completes actual.tree (extend completion child parent) ∧
        OwnedOn (Authority actual.tree (extend completion child parent) global.protectedTags target)
          lower upper actual.tree.locations := by
  obtain ⟨done,afterRuntime,capacity,growth,child,lookup,frame,completed,ancestry⟩ :=
    S05ConcreteProtectedChildCompletion.construct tree global completion runtime complete parentTag newTag parent parentNode
      tagged present fresh room tagBound held offset len nonzero bounds
  refine ⟨done,afterRuntime,capacity,growth,child,lookup,completed,?_⟩
  let rank := GeneralBorrowStructuralHistoryMutable.depth tree runtime.formed.toState
  let slot := GeneralBorrowStructuralHistoryMutable.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildMutable.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildMutable.append input
    have same : GeneralBorrowFreshMetadataChildMutable.index input = child := Option.some.inj (data.freshLookup.symm.trans lookup)
    have atEnd : (GeneralBorrowFreshMetadataChildMutable.index input).toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildMutable.at_end input
    have vacant : tree.nodes.get (GeneralBorrowFreshMetadataChildMutable.index input) = none := by
      simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _)]
    have clean : ∀ position (valid : position < tree.locations.entries.size),
        tree.locations.entries[position].data.perms.get (GeneralBorrowFreshMetadataChildMutable.index input) = none := by
      intro position valid
      exact (runtime.formed.profile position valid).vacant _ vacant
    have staged := stage_owned tree completion global.protectedTags complete (GeneralBorrowFreshMetadataChildMutable.index input)
      parent target parentNode targetNode newTag vacant present targetAt (GeneralBorrowFreshMetadataChildMutable.mapping input)
      offset len lower upper runtime.formed.well bounds disjoint clean owned
    have result := shape_owned (GeneralBorrowFreshMetadataChildMutable.stage input)
      (GeneralBorrowFreshMetadataChildMutable.result input) _ global.protectedTags target
      lower upper (GeneralBorrowFreshMetadataChildMutable.shape input) staged
    rw [same] at result
    simpa only [GeneralBorrowFreshMetadataChildMutable.result,input] using result
  | reuse index available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildMutableReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        index,available,bounded,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildMutableReuse.reuse input
    have same : index = child := Option.some.inj (data.freshLookup.symm.trans lookup)
    have clean : ∀ position (valid : position < tree.locations.entries.size),
        tree.locations.entries[position].data.perms.get index = none := by
      intro position valid
      exact (runtime.formed.profile position valid).vacant _ vacant
    have staged := stage_owned tree completion global.protectedTags complete index parent target parentNode targetNode newTag vacant present targetAt
      (GeneralBorrowFreshMetadataChildMutableReuse.mapping input) offset len lower upper runtime.formed.well bounds disjoint clean owned
    have result := shape_owned (GeneralBorrowFreshMetadataChildMutableReuse.stage input)
      (GeneralBorrowFreshMetadataChildMutableReuse.result input) _ global.protectedTags target
      lower upper (GeneralBorrowFreshMetadataChildMutableReuse.shape input) staged
    rw [same] at result
    simpa only [GeneralBorrowFreshMetadataChildMutableReuse.result,input] using result

end DuplicatePrefix.S05ConcreteProtectedChildDisjoint

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05ConcreteProtectedChildDisjoint." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved concrete protected disjoint dependency {dependency}"
