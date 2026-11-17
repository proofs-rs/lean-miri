import duplicate_prefix.GeneralBorrowDefaultConstructorFormed
import duplicate_prefix.GeneralBorrowExposureSifaTransport
import duplicate_prefix.GeneralBorrowSnapshotReadRuntime
namespace DuplicatePrefix.GeneralBorrowDefaultConstructorPossible
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowView GeneralBorrowProjection
open GeneralBorrowSnapshotReadRuntime (GlobalPossible)
open GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
attribute [local irreducible] UniValMap.insert

private theorem get_shape (location : LocationTree) (index : UniIndex) :
    (location.perms.get index).map stateShape = (locationShape location)[index.toNat]?.getD none := by
  unfold UniValMap.get locationShape
  simp only [Array.getElem?_map]
  cases location.perms.data[index.toNat]? <;> rfl

private theorem possible_shape (before after : LocationState) (same : stateShape after = stateShape before) : after.possible = before.possible := by
  rcases before with ⟨oldPermission,oldAccessed,oldSifa⟩
  rcases after with ⟨permission,accessed,sifa⟩
  simp only [stateShape,Prod.mk.injEq] at same
  rcases same with ⟨rfl,rfl⟩
  rfl

private theorem effective_shape (before after : LocationTree) (oldNode node : TreeNode) (index : UniIndex)
    (locations : locationShape after = locationShape before) (permission : node.defaultInitialPermission = oldNode.defaultInitialPermission) :
    stateShape ((after.perms.get index).getD node.defaultLocationState) =
      stateShape ((before.perms.get index).getD oldNode.defaultLocationState) := by
  have slots : (after.perms.get index).map stateShape = (before.perms.get index).map stateShape := by
    rw [get_shape,get_shape,locations]
  cases old : before.perms.get index with
  | none =>
    cases current : after.perms.get index with
    | none => simp only [old,current,Option.getD_none,stateShape,TreeNode.defaultLocationState,permission]
    | some state => simp [old,current] at slots
  | some previous =>
    cases current : after.perms.get index with
    | none => simp [old,current] at slots
    | some state => simpa only [old,current,Option.map_some,Option.some.injEq,Option.getD_some] using slots

/-- SIFA-preserved raw tree/row shape preserves global possible-state facts. -/
theorem shape (before after : BorrowTree) (same : treeShape after = treeShape before)
    (initial : Every (GlobalPossible before) before.locations) : Every (GlobalPossible after) after.locations := by
  have locations := congrArg (fun shape => shape.2.2.1) same
  change after.locations.entries.map (fun row => (row.range,locationShape row.data)) =
    before.locations.entries.map (fun row => (row.range,locationShape row.data)) at locations
  have sizes : after.locations.entries.size = before.locations.entries.size := by
    simpa only [Array.size_map] using congrArg Array.size locations
  intro position valid index node present
  have oldValid : position < before.locations.entries.size := by rw [←sizes];exact valid
  have rows := congrArg (fun values => values[position]?) locations
  simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,Array.getElem?_eq_getElem oldValid,
    Option.map_some,Option.some.injEq,Prod.mk.injEq] at rows
  obtain ⟨oldNode,oldPresent,_,_,_,permission⟩ := GeneralBorrowFreshMetadata.node_fields after before same.symm index node present
  have stateShape := effective_shape (before.locations.entries[position]'oldValid).data (after.locations.entries[position]'valid).data
    oldNode node index rows.2 permission.symm
  change ((after.locations.entries[position].data.perms.get index).getD node.defaultLocationState).possible = true
  rw [possible_shape _ _ stateShape]
  exact initial position oldValid index oldNode oldPresent

/-- Actual ancestor-SIFA updates preserve possible states, including every
physical row and lazy default. No success of the SIFA loop is assumed. -/
theorem sifa (tree : BorrowTree) (start : UniIndex) (strongest : IdempotentForeignAccess)
    (initial : Every (GlobalPossible tree) tree.locations) :
    Every (GlobalPossible (sourceUpdateSifa tree start strongest).1) (sourceUpdateSifa tree start strongest).1.locations :=
  shape tree _ (GeneralBorrowSifaView.preserves tree start strongest) initial

/-- Attaching a fresh mutable reservation preserves possible states. Vacant permission
Clean is consumed explicitly; vacancy alone does not imply it. -/
theorem attach (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (vacant : tree.nodes.get index = none) (present : tree.nodes.get parent = some parentNode)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (possible : GlobalPossible tree location) :
    GlobalPossible {tree with nodes := GeneralBorrowFreshNode.attachedNodes tree.nodes index parent parentNode (GeneralBorrowFreshDefaultChild.child tag parent)} location := by
  have different : index ≠ parent := by intro same;rw [same,present] at vacant;cases vacant
  have parentAfter : (tree.nodes.insert index (GeneralBorrowFreshDefaultChild.child tag parent)).get parent = some parentNode :=
    (GeneralBorrowFreshLocation.get_other _ index parent _ (Ne.symm different)).trans present
  intro query node found
  by_cases newIndex : query = index
  · subst query
    have freshPresent : ((tree.nodes.insert index (GeneralBorrowFreshDefaultChild.child tag parent)).insert parent
        (GeneralBorrowFreshGraph.updatedParent parentNode index)).get index = some (GeneralBorrowFreshDefaultChild.child tag parent) := by
      rw [GeneralBorrowFreshLocation.get_other _ parent index _ different,GeneralBorrowFreshLocation.get_same]
    change ((tree.nodes.insert index _).insert parent _).get index = some node at found
    have equal := Option.some.inj (freshPresent.symm.trans found)
    subst node
    change ((location.perms.get index).getD (GeneralBorrowFreshDefaultChild.child tag parent).defaultLocationState).possible = true
    rw [profile.vacant index vacant]
    rfl
  · by_cases isParent : query = parent
    · subst query
      change ((tree.nodes.insert index _).insert parent _).get parent = some node at found
      have lookup := GeneralBorrowNodeUpdate.insert_existing_get_same (tree.nodes.insert index (GeneralBorrowFreshDefaultChild.child tag parent)) parent parentNode
        (GeneralBorrowFreshGraph.updatedParent parentNode index) parentAfter
      have equal := Option.some.inj (lookup.symm.trans found)
      subst node
      exact possible parent parentNode present
    · change ((tree.nodes.insert index _).insert parent _).get query = some node at found
      rw [GeneralBorrowFreshLocation.get_other _ parent query _ isParent,
        GeneralBorrowFreshLocation.get_other _ index query _ newIndex] at found
      exact possible query node found

/-- Default inside materialization installs a possible accessed ReservedFrz(false) row and
frames every other present node. -/
theorem materialize (tree : BorrowTree) (location : LocationTree) (index : UniIndex)
    (possible : GlobalPossible tree location) :
    GlobalPossible tree (GeneralBorrowFreshMaterialization.materialized location index GeneralBorrowFreshDefaultChild.inside) := by
  intro query node present
  by_cases same : query = index
  · subst query
    simp only [GeneralBorrowFreshMaterialization.materialized,GeneralBorrowWildcardVirtualLeaf.effective,GeneralBorrowFreshLocation.get_same,Option.getD_some]
    rfl
  · simpa only [GeneralBorrowFreshMaterialization.materialized,GeneralBorrowWildcardVirtualLeaf.effective,GeneralBorrowFreshLocation.get_other _ index query _ same] using possible query node present

/-- Full actual Default mutable range-installation and ancestor-SIFA stage preserves
possible states, using only initial physical possible/Clean resources. -/
theorem default_stage (tree : BorrowTree) (protections : ProtectedTags)
    (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag) (mapping : UniKeyMap BorTag)
    (vacant : tree.nodes.get index = none) (present : tree.nodeAt parent = some parentNode)
    (offset len : UInt64) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (profile : Every (fun location => GeneralBorrowLocationSifaConsistency.Profile tree location protections) tree.locations)
    (possible : Every (GlobalPossible tree) tree.locations) :
    let staged := GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode
      (GeneralBorrowFreshDefaultChild.child tag parent) mapping
      (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
        (fun _ location => GeneralBorrowFreshMaterialization.materialized location index GeneralBorrowFreshDefaultChild.inside)).state
    Every (GlobalPossible (sourceUpdateSifa staged parent .Read).1) (sourceUpdateSifa staged parent .Read).1.locations := by
  let base := {tree with nodes := GeneralBorrowFreshNode.attachedNodes tree.nodes index parent parentNode (GeneralBorrowFreshDefaultChild.child tag parent)}
  have attached : Every (GlobalPossible base) tree.locations := by
    intro position valid
    exact attach tree _ protections index parent parentNode tag vacant present (profile position valid) (possible position valid)
  have modified := GeneralBorrowExposureChildAttach.modify_every (GlobalPossible base) tree.locations
    (Size.ofBytes offset) (Size.ofBytes len)
    (fun _ location => GeneralBorrowFreshMaterialization.materialized location index GeneralBorrowFreshDefaultChild.inside)
    well bounds attached (by intro range location good;exact materialize base location index good)
  exact sifa _ parent .Read modified

end DuplicatePrefix.GeneralBorrowDefaultConstructorPossible
