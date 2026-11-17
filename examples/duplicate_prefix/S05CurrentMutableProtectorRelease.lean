import duplicate_prefix.S05CurrentReleaseIterator
import duplicate_prefix.S05CompletedAncestryReadMutable
import duplicate_prefix.S05CompletedAncestryConcreteWrite
import duplicate_prefix.S05CompletedWriteAuthorityConcrete
import duplicate_prefix.GeneralBorrowFreshActiveWithin
import duplicate_prefix.DuplicatePrefixBorrowContract
import duplicate_prefix.S02HiddenLeafQuietTreeAccess
namespace DuplicatePrefix.S05CurrentMutableProtectorRelease
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowProjection
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality GeneralRangeMapOrigins GeneralRangeMapState BorrowRangeAccess
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
noncomputable section
private theorem completion_locations (tree : BorrowTree) (completion : Completion)
    (locations : DedupRangeMap LocationTree) (complete : Completes tree completion) :
    Completes {tree with locations := locations} completion := by
  refine ⟨complete.1,complete.2.1,complete.2.2.1,complete.2.2.2.1,complete.2.2.2.2.1,?_,complete.2.2.2.2.2.2⟩
  intro position root slot
  have original := complete.2.2.2.2.2.1 position root slot
  by_cases zero : position = 0
  · simpa only [zero,↓reduceIte] using original
  · simp only [zero,↓reduceIte] at original ⊢
    obtain ⟨earlier,originRoot,origin,rootNode,originNode,older,earlierSlot,rootHere,originHere,exposed,ordered,path,parent⟩ := original
    exact ⟨earlier,originRoot,origin,rootNode,originNode,older,earlierSlot,rootHere,originHere,exposed,ordered,
      GeneralBorrowPrimaryWitnessVisibility.path_nodes (before := {tree with locations := locations}) (after := tree) rfl path,parent⟩
theorem release_runtime (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : Completes tree completion)
    (order : ParentTagOrder tree)
    (selectedPosition : Nat) (selected source : UniIndex) (selectedNode sourceNode : TreeNode)
    (selectedSlot : tree.roots[selectedPosition]? = some selected)
    (selectedPresent : tree.nodes.get selected = some selectedNode) (sourcePath : Path tree selected source)
    (sourcePresent : tree.nodes.get source = some sourceNode)
    (hidden : sourceNode.isExposed = false) (offset len : UInt64)
    (positive : offset.toNat < (offset+len).toNat)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree source .Write offset (offset+len))
    (owned : OwnedOn (S05CompletedAncestryReadMutable.Authority tree completion global.protectedTags source) offset (offset+len) tree.locations)
    (short : tree.nodes.size < 65536) :
    let result := tree.releaseProtector sourceNode.tag global.protectedTags
    result.status = .Released ∧ result.tree = {tree with locations := result.tree.locations} ∧
    DuplicatePrefixBorrowContract.RuntimeFacts result.tree global ∧ Completes result.tree completion ∧
    result.tree.locations.size = tree.locations.size := by
  let P := fun (_ : ByteRange) (location : LocationTree) =>
    LocationCoherent tree location global.protectedTags ∧
      GeneralBorrowLocationSifaConsistency.Profile tree location global.protectedTags ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location
  have rows : S05CurrentReleaseIterator.Rows P tree.locations := by
    intro position valid
    exact ⟨runtime.coherent position valid,runtime.formed.profile position valid,runtime.possible position valid⟩
  have activeRows := GeneralBorrowFreshActiveWithin.active_on tree source .Write offset (offset+len) runtime.formed.well active
  obtain ⟨depth⟩ := runtime.formed.depth
  have mapped := (complete.2.2.2.2.1 source sourceNode sourcePresent).1
  obtain ⟨done,frame,afterRows,well,ranges,capacity⟩ := S05CurrentReleaseIterator.release tree global.protectedTags
    sourceNode.tag source sourceNode sourcePresent hidden mapped P rows runtime.formed.well (by
      intro position valid state stored accessed kind associated
      obtain ⟨start,stop,_⟩ := activeRows position valid state stored accessed kind associated
      have authority := owned position valid positive start stop
      have current := rows position valid
      cases kind with
      | Read =>
        have result := S05CompletedAncestryReadMutable.access tree completion tree.locations.entries[position].data global.protectedTags
          complete runtime.formed.toGraphState depth order selectedPosition selected source selectedNode selectedSlot selectedPresent sourcePath
          authority current.1 current.2.1 current.2.2 short .SkipChildrenOfAccessed tree.locations.entries[position].range
        exact ⟨result.1,result.2.1,result.2.2.1,result.2.2.2.1⟩
      | Write =>
        have result := S05CompletedAncestryConcreteWrite.access tree completion tree.locations.entries[position].data global.protectedTags
          complete runtime.formed.toGraphState depth order selectedPosition selected source selectedNode selectedSlot selectedPresent sourcePath
          (fun index node present _ => (authority index node present).1)
          (fun index node present _ => (authority index node present).2)
          (fun _ _ _ _ index node present _ => (authority index node present).1)
          (fun _ _ _ _ index node present _ => (authority index node present).2)
          current.1 current.2.1 current.2.2 short .SkipChildrenOfAccessed tree.locations.entries[position].range
        exact ⟨result.1,result.2.1,result.2.2.1,result.2.2.2.1⟩)
  refine ⟨done,frame,?_,?_,capacity⟩
  · rw [frame]
    have graph := GeneralBorrowStructuralHistoryState.graph_locations tree (tree.releaseProtector sourceNode.tag global.protectedTags).tree.locations runtime.formed.toGraphState
    refine ⟨⟨⟨graph,well⟩,?_⟩,?_,?_,⟨runtime.below.mapping,runtime.below.protectors⟩⟩
    · intro position valid
      have profile := (afterRows position valid).2.1
      exact ⟨profile.present,profile.vacant⟩
    · intro position valid
      exact (afterRows position valid).1
    · intro position valid
      exact (afterRows position valid).2.2
  · rw [frame]
    exact completion_locations tree completion _ complete
theorem release_preserving_disjoint (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : Completes tree completion)
    (order : ParentTagOrder tree)
    (selectedPosition : Nat) (selected source : UniIndex) (selectedNode sourceNode : TreeNode)
    (selectedSlot : tree.roots[selectedPosition]? = some selected)
    (selectedPresent : tree.nodes.get selected = some selectedNode) (sourcePath : Path tree selected source)
    (sourcePresent : tree.nodes.get source = some sourceNode)
    (hidden : sourceNode.isExposed = false) (offset len : UInt64)
    (positive : offset.toNat < (offset+len).toNat)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree source .Write offset (offset+len))
    (owned : OwnedOn (S05CompletedAncestryReadMutable.Authority tree completion global.protectedTags source) offset (offset+len) tree.locations)
    (targetLower targetUpper : UInt64) (targetPositive : targetLower.toNat < targetUpper.toNat) (targetPredicate : LocationTree → Prop)
    (disjoint : (offset+len).toNat ≤ targetLower.toNat ∨ targetUpper.toNat ≤ offset.toNat)
    (targetOwned : OwnedOn targetPredicate targetLower targetUpper tree.locations)
    (short : tree.nodes.size < 65536) :
    let result := tree.releaseProtector sourceNode.tag global.protectedTags
    result.status = .Released ∧ result.tree = {tree with locations := result.tree.locations} ∧
    DuplicatePrefixBorrowContract.RuntimeFacts result.tree global ∧ Completes result.tree completion ∧
    result.tree.locations.size = tree.locations.size ∧
    OwnedOn targetPredicate targetLower targetUpper result.tree.locations := by
  let P := fun (range : ByteRange) (location : LocationTree) =>
    LocationCoherent tree location global.protectedTags ∧
      GeneralBorrowLocationSifaConsistency.Profile tree location global.protectedTags ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location ∧
      (range.start.toNat < targetUpper.toNat → targetLower.toNat < range.stop.toNat → targetPredicate location)
  have rows : S05CurrentReleaseIterator.Rows P tree.locations := by
    intro position valid
    exact ⟨runtime.coherent position valid,runtime.formed.profile position valid,runtime.possible position valid,
      fun start stop => targetOwned position valid targetPositive start stop⟩
  have activeRows := GeneralBorrowFreshActiveWithin.active_on tree source .Write offset (offset+len) runtime.formed.well active
  obtain ⟨depth⟩ := runtime.formed.depth
  have mapped := (complete.2.2.2.2.1 source sourceNode sourcePresent).1
  obtain ⟨done,frame,afterRows,well,ranges,capacity⟩ := S05CurrentReleaseIterator.release tree global.protectedTags
    sourceNode.tag source sourceNode sourcePresent hidden mapped P rows runtime.formed.well (by
      intro position valid state stored accessed kind associated
      obtain ⟨start,stop,_⟩ := activeRows position valid state stored accessed kind associated
      have authority := owned position valid positive start stop
      have current := rows position valid
      have outside : ¬ (tree.locations.entries[position].range.start.toNat < targetUpper.toNat ∧
          targetLower.toNat < tree.locations.entries[position].range.stop.toNat) := by
        have activeAtStart := active tree.locations.entries[position].range.start tree.locations.entries[position].data
          ⟨position,valid,Nat.le_refl _,(GeneralRangeMapGeometry.facts tree.locations runtime.formed.well (by omega)).2.1 position valid,rfl⟩
          state stored accessed kind associated
        -- Whole active rows lie inside the source interval by pointwise activity.
        have insideStop : tree.locations.entries[position].range.stop.toNat ≤ (offset+len).toNat := by
          by_cases greater : tree.locations.entries[position].range.stop.toNat ≤ (offset+len).toNat
          · exact greater
          have atEnd := active (offset+len) tree.locations.entries[position].data
            ⟨position,valid,by omega,by omega,rfl⟩ state stored accessed kind associated
          omega
        intro overlaps
        rcases disjoint with left | right <;> omega
      cases kind with
      | Read =>
        have result := S05CompletedAncestryReadMutable.access tree completion tree.locations.entries[position].data global.protectedTags
          complete runtime.formed.toGraphState depth order selectedPosition selected source selectedNode selectedSlot selectedPresent sourcePath
          authority current.1 current.2.1 current.2.2.1 short .SkipChildrenOfAccessed tree.locations.entries[position].range
        exact ⟨result.1,result.2.1,result.2.2.1,result.2.2.2.1,fun start stop => False.elim (outside ⟨start,stop⟩)⟩
      | Write =>
        have result := S05CompletedAncestryConcreteWrite.access tree completion tree.locations.entries[position].data global.protectedTags
          complete runtime.formed.toGraphState depth order selectedPosition selected source selectedNode selectedSlot selectedPresent sourcePath
          (fun index node present _ => (authority index node present).1)
          (fun index node present _ => (authority index node present).2)
          (fun _ _ _ _ index node present _ => (authority index node present).1)
          (fun _ _ _ _ index node present _ => (authority index node present).2)
          current.1 current.2.1 current.2.2.1 short .SkipChildrenOfAccessed tree.locations.entries[position].range
        exact ⟨result.1,result.2.1,result.2.2.1,result.2.2.2.1,fun start stop => False.elim (outside ⟨start,stop⟩)⟩)
  refine ⟨done,frame,?_,?_,capacity,?_⟩
  · rw [frame]
    have graph := GeneralBorrowStructuralHistoryState.graph_locations tree (tree.releaseProtector sourceNode.tag global.protectedTags).tree.locations runtime.formed.toGraphState
    refine ⟨⟨⟨graph,well⟩,?_⟩,?_,?_,⟨runtime.below.mapping,runtime.below.protectors⟩⟩
    · intro position valid
      have profile := (afterRows position valid).2.1
      exact ⟨profile.present,profile.vacant⟩
    · intro position valid
      exact (afterRows position valid).1
    · intro position valid
      exact (afterRows position valid).2.2.1
  · rw [frame]
    exact completion_locations tree completion _ complete
  · intro position valid _ start stop
    exact (afterRows position valid).2.2.2 start stop

theorem release_preserving_disjoint_activity (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : Completes tree completion)
    (order : ParentTagOrder tree)
    (selectedPosition : Nat) (selected source : UniIndex) (selectedNode sourceNode : TreeNode)
    (selectedSlot : tree.roots[selectedPosition]? = some selected)
    (selectedPresent : tree.nodes.get selected = some selectedNode) (sourcePath : Path tree selected source)
    (sourcePresent : tree.nodes.get source = some sourceNode)
    (hidden : sourceNode.isExposed = false) (offset len : UInt64)
    (positive : offset.toNat < (offset+len).toNat)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree source .Write offset (offset+len))
    (owned : OwnedOn (S05CompletedAncestryReadMutable.Authority tree completion global.protectedTags source) offset (offset+len) tree.locations)
    (targetLower targetUpper : UInt64) (targetPositive : targetLower.toNat < targetUpper.toNat) (targetPredicate : LocationTree → Prop)
    (disjoint : (offset+len).toNat ≤ targetLower.toNat ∨ targetUpper.toNat ≤ offset.toNat)
    (targetOwned : OwnedOn targetPredicate targetLower targetUpper tree.locations)
    (target : UniIndex) (targetNode : TreeNode) (targetAt : tree.nodeAt target = some targetNode)
    (targetLeaf : targetNode.children = #[]) (targetHidden : targetNode.isExposed = false) (different : target ≠ source)
    (targetActive : GeneralBorrowFreshActiveWithin.ActiveWithin tree target .Write targetLower targetUpper)
    (short : tree.nodes.size < 65536) :
    let result := tree.releaseProtector sourceNode.tag global.protectedTags
    result.status = .Released ∧ result.tree = {tree with locations := result.tree.locations} ∧
    DuplicatePrefixBorrowContract.RuntimeFacts result.tree global ∧ Completes result.tree completion ∧
    result.tree.locations.size = tree.locations.size ∧
    OwnedOn targetPredicate targetLower targetUpper result.tree.locations ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin result.tree target .Write targetLower targetUpper := by
  let P := fun (range : ByteRange) (location : LocationTree) =>
    LocationCoherent tree location global.protectedTags ∧
      GeneralBorrowLocationSifaConsistency.Profile tree location global.protectedTags ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location ∧
      (range.start.toNat < targetUpper.toNat → targetLower.toNat < range.stop.toNat → targetPredicate location) ∧
      (∀ point : UInt64, range.start.toNat ≤ point.toNat → point.toNat < range.stop.toNat →
        ∀ state, location.perms.get target = some state → state.accessed = true →
        ∀ kind, state.permission.associatedAccess = some kind → targetLower.toNat ≤ point.toNat ∧ point.toNat < targetUpper.toNat)
  have rows : S05CurrentReleaseIterator.Rows P tree.locations := by
    intro position valid
    exact ⟨runtime.coherent position valid,runtime.formed.profile position valid,runtime.possible position valid,
      (fun start stop => targetOwned position valid targetPositive start stop),by
        intro point start stop state stored accessed kind associated
        have old := targetActive point tree.locations.entries[position].data ⟨position,valid,start,stop,rfl⟩ state stored accessed kind associated
        exact ⟨old.1,old.2.1⟩⟩
  have activeRows := GeneralBorrowFreshActiveWithin.active_on tree source .Write offset (offset+len) runtime.formed.well active
  obtain ⟨depth⟩ := runtime.formed.depth
  have mapped := (complete.2.2.2.2.1 source sourceNode sourcePresent).1
  obtain ⟨done,frame,afterRows,well,ranges,capacity⟩ := S05CurrentReleaseIterator.release tree global.protectedTags
    sourceNode.tag source sourceNode sourcePresent hidden mapped P rows runtime.formed.well (by
      intro position valid state stored accessed kind associated
      obtain ⟨start,stop,_⟩ := activeRows position valid state stored accessed kind associated
      have authority := owned position valid positive start stop
      have current := rows position valid
      have outside : ¬ (tree.locations.entries[position].range.start.toNat < targetUpper.toNat ∧
          targetLower.toNat < tree.locations.entries[position].range.stop.toNat) := by
        have activeAtStart := active tree.locations.entries[position].range.start tree.locations.entries[position].data
          ⟨position,valid,Nat.le_refl _,(GeneralRangeMapGeometry.facts tree.locations runtime.formed.well (by omega)).2.1 position valid,rfl⟩
          state stored accessed kind associated
        -- Whole active rows lie inside the source interval by pointwise activity.
        have insideStop : tree.locations.entries[position].range.stop.toNat ≤ (offset+len).toNat := by
          by_cases greater : tree.locations.entries[position].range.stop.toNat ≤ (offset+len).toNat
          · exact greater
          have atEnd := active (offset+len) tree.locations.entries[position].data
            ⟨position,valid,by omega,by omega,rfl⟩ state stored accessed kind associated
          omega
        intro overlaps
        rcases disjoint with left | right <;> omega
      have nextActive : ∀ point : UInt64, tree.locations.entries[position].range.start.toNat ≤ point.toNat →
          point.toNat < tree.locations.entries[position].range.stop.toNat → ∀ state,
          (source_access_location (source_tree_access_at tree tree.locations.entries[position].data (some source) kind global.protectedTags
            .SkipChildrenOfAccessed tree.locations.entries[position].range)).perms.get target = some state → state.accessed = true →
          ∀ accessKind, state.permission.associatedAccess = some accessKind → targetLower.toNat ≤ point.toNat ∧ point.toNat < targetUpper.toNat := by
        intro point atStart atStop state afterStored afterAccessed accessKind afterAssociated
        by_cases inside : targetLower.toNat ≤ point.toNat ∧ point.toNat < targetUpper.toNat
        · exact inside
        have quiet : S02HiddenLeafQuietNormal.Quiet (GeneralBorrowWildcardVirtualLeaf.effective tree.locations.entries[position].data target targetNode) := by
          cases beforeStored : tree.locations.entries[position].data.perms.get target with
          | none => left;simp only [GeneralBorrowWildcardVirtualLeaf.effective,beforeStored,Option.getD_none,TreeNode.defaultLocationState]
          | some old =>
            simp only [GeneralBorrowWildcardVirtualLeaf.effective,beforeStored,Option.getD_some]
            by_cases cell : old.permission = .Cell
            · exact .inr cell
            · left
              cases h : old.accessed with
              | false => rfl
              | true =>
                have associated : ∃ k,old.permission.associatedAccess = some k := by cases p : old.permission <;> simp_all [Permission.associatedAccess]
                obtain ⟨k,associated⟩ := associated
                exact False.elim (inside (current.2.2.2.2 point atStart atStop old beforeStored h k associated))
        obtain ⟨normal⟩ := S05CompletedAncestryNormal.normal tree completion tree.locations.entries[position].data global.protectedTags complete
          runtime.formed.toGraphState depth runtime.formed.fits selectedPosition selected source selectedNode selectedSlot selectedPresent sourcePath
          (fun index node present _ => (authority index node present).1) (fun index node present _ => (authority index node present).2)
        have afterQuiet := (S02HiddenLeafQuietTreeAccess.concrete tree runtime.formed.toGraphState tree.locations.entries[position].data global.protectedTags
          target source targetNode sourceNode targetAt sourcePresent targetLeaf targetHidden different normal current.1 kind .SkipChildrenOfAccessed
          tree.locations.entries[position].range quiet).1
        change S02HiddenLeafQuietNormal.Quiet (((source_access_location (source_tree_access_at tree tree.locations.entries[position].data (some source) kind global.protectedTags
          .SkipChildrenOfAccessed tree.locations.entries[position].range)).perms.get target).getD targetNode.defaultLocationState) at afterQuiet
        rw [afterStored] at afterQuiet
        rcases afterQuiet with inactive | cell
        · simp only [Option.getD_some] at inactive;rw [afterAccessed] at inactive;cases inactive
        · simp only [Option.getD_some] at cell;rw [cell,Permission.associatedAccess] at afterAssociated;cases afterAssociated
      cases kind with
      | Read =>
        have result := S05CompletedAncestryReadMutable.access tree completion tree.locations.entries[position].data global.protectedTags
          complete runtime.formed.toGraphState depth order selectedPosition selected source selectedNode selectedSlot selectedPresent sourcePath
          authority current.1 current.2.1 current.2.2.1 short .SkipChildrenOfAccessed tree.locations.entries[position].range
        exact ⟨result.1,result.2.1,result.2.2.1,result.2.2.2.1,(fun start stop => False.elim (outside ⟨start,stop⟩)),nextActive⟩
      | Write =>
        have result := S05CompletedAncestryConcreteWrite.access tree completion tree.locations.entries[position].data global.protectedTags
          complete runtime.formed.toGraphState depth order selectedPosition selected source selectedNode selectedSlot selectedPresent sourcePath
          (fun index node present _ => (authority index node present).1)
          (fun index node present _ => (authority index node present).2)
          (fun _ _ _ _ index node present _ => (authority index node present).1)
          (fun _ _ _ _ index node present _ => (authority index node present).2)
          current.1 current.2.1 current.2.2.1 short .SkipChildrenOfAccessed tree.locations.entries[position].range
        exact ⟨result.1,result.2.1,result.2.2.1,result.2.2.2.1,(fun start stop => False.elim (outside ⟨start,stop⟩)),nextActive⟩)
  refine ⟨done,frame,?_,?_,capacity,?_,?_⟩
  · rw [frame]
    have graph := GeneralBorrowStructuralHistoryState.graph_locations tree (tree.releaseProtector sourceNode.tag global.protectedTags).tree.locations runtime.formed.toGraphState
    refine ⟨⟨⟨graph,well⟩,?_⟩,?_,?_,⟨runtime.below.mapping,runtime.below.protectors⟩⟩
    · intro position valid
      have profile := (afterRows position valid).2.1
      exact ⟨profile.present,profile.vacant⟩
    · intro position valid
      exact (afterRows position valid).1
    · intro position valid
      exact (afterRows position valid).2.2.1
  · rw [frame]
    exact completion_locations tree completion _ complete
  · intro position valid _ start stop
    exact (afterRows position valid).2.2.2.1 start stop
  · intro point location atPoint state stored accessed kind associated
    obtain ⟨position,valid,start,stop,dataEq⟩ := atPoint
    have inside := (afterRows position valid).2.2.2.2 point start stop state (by rw [dataEq];exact stored) accessed kind associated
    exact ⟨inside.1,inside.2,by intro impossible;cases impossible⟩

theorem release_owned (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : Completes tree completion)
    (order : ParentTagOrder tree)
    (selectedPosition : Nat) (selected source : UniIndex) (selectedNode sourceNode : TreeNode)
    (selectedSlot : tree.roots[selectedPosition]? = some selected)
    (selectedPresent : tree.nodes.get selected = some selectedNode) (sourcePath : Path tree selected source)
    (sourcePresent : tree.nodes.get source = some sourceNode)
    (hidden : sourceNode.isExposed = false) (offset len : UInt64)
    (positive : offset.toNat < (offset+len).toNat)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree source .Write offset (offset+len))
    (owned : OwnedOn (S05CompletedAncestryReadMutable.Authority tree completion global.protectedTags source) offset (offset+len) tree.locations)
    (short : tree.nodes.size < 65536) :
    let result := tree.releaseProtector sourceNode.tag global.protectedTags
    result.status = .Released ∧ result.tree = {tree with locations := result.tree.locations} ∧
    DuplicatePrefixBorrowContract.RuntimeFacts result.tree global ∧ Completes result.tree completion ∧
    result.tree.locations.size = tree.locations.size ∧
    OwnedOn (S05CompletedAncestryReadMutable.Authority result.tree completion global.protectedTags source)
      offset (offset+len) result.tree.locations := by
  let P := fun (range : ByteRange) (location : LocationTree) =>
    LocationCoherent tree location global.protectedTags ∧
      GeneralBorrowLocationSifaConsistency.Profile tree location global.protectedTags ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location ∧
      (range.start.toNat < (offset+len).toNat → offset.toNat < range.stop.toNat →
        S05CompletedAncestryReadMutable.Authority tree completion global.protectedTags source location)
  have rows : S05CurrentReleaseIterator.Rows P tree.locations := by
    intro position valid
    exact ⟨runtime.coherent position valid,runtime.formed.profile position valid,runtime.possible position valid,
      fun start stop => owned position valid positive start stop⟩
  have activeRows := GeneralBorrowFreshActiveWithin.active_on tree source .Write offset (offset+len) runtime.formed.well active
  obtain ⟨depth⟩ := runtime.formed.depth
  have mapped := (complete.2.2.2.2.1 source sourceNode sourcePresent).1
  obtain ⟨done,frame,afterRows,well,ranges,capacity⟩ := S05CurrentReleaseIterator.release tree global.protectedTags
    sourceNode.tag source sourceNode sourcePresent hidden mapped P rows runtime.formed.well (by
      intro position valid state stored accessed kind associated
      obtain ⟨start,stop,_⟩ := activeRows position valid state stored accessed kind associated
      have authority := owned position valid positive start stop
      have current := rows position valid
      cases kind with
      | Read =>
        have result := S05CompletedAncestryReadMutable.access tree completion tree.locations.entries[position].data global.protectedTags
          complete runtime.formed.toGraphState depth order selectedPosition selected source selectedNode selectedSlot selectedPresent sourcePath
          authority current.1 current.2.1 current.2.2.1 short .SkipChildrenOfAccessed tree.locations.entries[position].range
        exact ⟨result.1,result.2.1,result.2.2.1,result.2.2.2.1,fun _ _ => result.2.2.2.2⟩
      | Write =>
        have result := S05CompletedWriteAuthorityConcrete.access tree completion tree.locations.entries[position].data global.protectedTags
          complete runtime.formed.toGraphState depth order selectedPosition selected source selectedNode selectedSlot selectedPresent sourcePath
          authority current.1 current.2.1 current.2.2.1 short .SkipChildrenOfAccessed tree.locations.entries[position].range
        exact ⟨result.1,result.2.1,result.2.2.1,result.2.2.2.1,fun _ _ => result.2.2.2.2⟩)
  refine ⟨done,frame,?_,?_,capacity,?_⟩
  · rw [frame]
    have graph := GeneralBorrowStructuralHistoryState.graph_locations tree (tree.releaseProtector sourceNode.tag global.protectedTags).tree.locations runtime.formed.toGraphState
    refine ⟨⟨⟨graph,well⟩,?_⟩,?_,?_,⟨runtime.below.mapping,runtime.below.protectors⟩⟩
    · intro position valid
      have profile := (afterRows position valid).2.1
      exact ⟨profile.present,profile.vacant⟩
    · intro position valid
      exact (afterRows position valid).1
    · intro position valid
      exact (afterRows position valid).2.2.1
  · rw [frame]
    exact completion_locations tree completion _ complete
  · rw [frame]
    intro position valid _ start stop index node present
    exact (afterRows position valid).2.2.2 start stop index node present

end
end DuplicatePrefix.S05CurrentMutableProtectorRelease
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05CurrentMutableProtectorRelease." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved mutable release runtime dependency {dependency}"
