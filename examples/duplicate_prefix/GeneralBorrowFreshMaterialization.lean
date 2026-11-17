import duplicate_prefix.GeneralBorrowFreshProjection
import duplicate_prefix.GeneralBorrowFreshEntries
import duplicate_prefix.GeneralBorrowFreshOwnership
namespace DuplicatePrefix.GeneralBorrowFreshMaterialization
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowFreshNode
open DuplicatePrefix.GeneralBorrowNodeUpdate
set_option maxRecDepth 65536
set_option maxHeartbeats 100000

private theorem entries_push {α : Type} (map : UniValMap α) (index : UniIndex) (value : α)
    (atEnd : index.toNat = map.data.size) :
    (⟨map.data.push (some value)⟩ : UniValMap α).entries = map.entries.push (index,value) := by
  have old : (List.range' 0 map.data.size).filterMap (GeneralBorrowFreshEntries.slot (map.data.push (some value))) =
      (List.range' 0 map.data.size).filterMap (GeneralBorrowFreshEntries.slot map.data) := by
    have maps : (List.range' 0 map.data.size).map (GeneralBorrowFreshEntries.slot (map.data.push (some value))) =
        (List.range' 0 map.data.size).map (GeneralBorrowFreshEntries.slot map.data) := by
      apply List.map_congr_left
      intro position member
      have valid : position < map.data.size := by have := (List.mem_range'_1.mp member).2;omega
      have different : position ≠ map.data.size := by omega
      simp only [GeneralBorrowFreshEntries.slot,Array.getElem?_push,valid,different,↓reduceIte]
    simpa only [List.filterMap_map,Function.comp_def,id_eq] using congrArg (List.filterMap id) maps
  have converted : UniIndex.ofNat? map.data.size = some index := by rw [←atEnd];exact index_self index
  have last : GeneralBorrowFreshEntries.slot (map.data.push (some value)) map.data.size = some (index,value) := by
    simp [GeneralBorrowFreshEntries.slot,converted]
  rw [GeneralBorrowFreshEntries.entries_formula,GeneralBorrowFreshEntries.entries_formula]
  simp only [Array.size_push,List.range'_concat,Nat.zero_add,Nat.one_mul,List.filterMap_append,old]
  simp only [List.filterMap_cons_some last,List.filterMap_nil]
  simp

private theorem attached_tags (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode) :
    (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode).nodes.data.map (Option.map TreeNode.tag) =
      (tree.nodes.data.map (Option.map TreeNode.tag)).push (some newNode.tag) := by
  have old : (tree.nodes.insert index newNode).get parent = some parentNode :=
    (append_get_other tree.nodes index parent newNode atEnd
      (parent_not_fresh tree.nodes index parent parentNode atEnd parentPresent)).trans parentPresent
  have same := GeneralBorrowView.insert_existing_shape TreeNode.tag (tree.nodes.insert index newNode) parent parentNode
    {parentNode with children := parentNode.children.push index} old rfl
  dsimp only [GeneralBorrowFreshGraph.attached,attachedNodes]
  rw [same,insert_append tree.nodes index newNode atEnd]
  simp only [Array.map_push,Option.map_some]

private theorem tagged_entries (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode) :
    (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode).nodes.entries.map (fun row => (row.1,row.2.tag)) =
      (tree.nodes.entries.map (fun row => (row.1,row.2.tag))).push (index,newNode.tag) := by
  rw [←GeneralBorrowFreshEntries.entries_map TreeNode.tag,
    attached_tags tree index parent parentNode newNode atEnd parentPresent]
  rw [entries_push (⟨tree.nodes.data.map (Option.map TreeNode.tag)⟩ : UniValMap BorTag) index newNode.tag
    (by simpa only [Array.size_map] using atEnd)]
  rw [GeneralBorrowFreshEntries.entries_map TreeNode.tag tree.nodes]

private def protectionIndex (protections : ProtectedTags) (row : UniIndex × BorTag) : Option Nat :=
  if protections.contains row.2 then some row.1.toNat else none

private theorem protections_via_tags (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection tree location protections).protectedNodes =
      (tree.nodes.entries.map (fun row => (row.1,row.2.tag))).toList.filterMap (protectionIndex protections) := by
  unfold_general_projection
  simp only [Array.toList_map,List.filterMap_map,Function.comp_def,protectionIndex]

/-- Actual child insertion adds only the new tag's protection index. Existing
protection membership is not assumed and can include arbitrary caller history. -/
theorem protections_exact (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (oldLocation newLocation : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode) newLocation protections).protectedNodes =
      (source_normal_projection tree oldLocation protections).protectedNodes ++
        if protections.contains newNode.tag then [index.toNat] else [] := by
  rw [protections_via_tags,protections_via_tags,tagged_entries tree index parent parentNode newNode atEnd parentPresent]
  simp only [Array.toList_push,List.filterMap_append]
  cases held : protections.contains newNode.tag <;> simp [protectionIndex,held]

def materialized (location : LocationTree) (index : UniIndex) (state : LocationState) : LocationTree :=
  {location with perms := location.perms.insert index state}

private def absentDefault : LocationState := ⟨.Disabled,false,.None⟩

private theorem projection_slot (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (position : Nat) (query : UniIndex) (converted : UniIndex.ofNat? position = some query)
    (equal : query.toNat = position) (valid : position < tree.nodes.data.size) :
    (source_normal_projection tree location protections).stateAt position =
      some ((location.perms.get query).getD (((tree.nodeAt query).map TreeNode.defaultLocationState).getD absentDefault)) := by
  have nodeValue : tree.nodeAt query = tree.nodes.data[position]'valid := by
    unfold BorrowTree.nodeAt UniValMap.get
    simp only [equal,Array.getElem?_eq_getElem valid]
  unfold_general_projection
  unfold NormalTreeState.stateAt
  simp only [Array.getElem?_mapIdx,Array.getElem?_map,Array.getElem?_eq_getElem valid,
    converted,Option.map_some]
  rw [nodeValue]
  generalize stateEq : location.perms.get query = stored
  clear stateEq
  generalize nodeEq : tree.nodes.data[position] = node
  clear nodeEq
  cases stored <;> cases node <;> rfl

private theorem attached_size (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode) :
    (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode).nodes.data.size = tree.nodes.data.size+1 := by
  have old : (tree.nodes.insert index newNode).get parent = some parentNode :=
    (append_get_other tree.nodes index parent newNode atEnd
      (parent_not_fresh tree.nodes index parent parentNode atEnd parentPresent)).trans parentPresent
  change ((tree.nodes.insert index newNode).insert parent {parentNode with children := parentNode.children.push index}).size = tree.nodes.size+1
  rw [insert_existing_size (tree.nodes.insert index newNode) parent parentNode _ old,append_size tree.nodes index newNode atEnd]

private theorem old_default (tree : BorrowTree) (index parent query : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (different : query ≠ index) :
    (((GeneralBorrowFreshGraph.attached tree index parent parentNode newNode).nodeAt query).map TreeNode.defaultLocationState).getD absentDefault =
      ((tree.nodeAt query).map TreeNode.defaultLocationState).getD absentDefault := by
  by_cases same : query = parent
  · subst query
    rw [GeneralBorrowFreshGraph.parent_lookup tree index parent parentNode newNode atEnd parentPresent,parentPresent]
    rfl
  · rw [GeneralBorrowFreshGraph.other_lookup tree index parent query parentNode newNode atEnd parentPresent same different]

/-- Materializing the fresh child's permission preserves every old projected
state, including missing node slots and sparse permission-map gaps. -/
theorem state_old (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (location : LocationTree) (state : LocationState) (protections : ProtectedTags)
    (position : Nat) (valid : position < tree.nodes.data.size) :
    (source_normal_projection (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode)
      (materialized location index state) protections).stateAt position =
      (source_normal_projection tree location protections).stateAt position := by
  have indexBound : index.toNat < 4294967296 := UInt32.toNat_lt index.idx
  obtain ⟨query,converted,equal⟩ := index_nat position (by omega)
  have different : query ≠ index := by
    intro same
    have known := congrArg UniIndex.toNat same
    rw [equal,atEnd] at known
    omega
  have validAfter : position < (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode).nodes.data.size := by
    rw [attached_size tree index parent parentNode newNode atEnd parentPresent]
    omega
  rw [projection_slot _ _ _ position query converted equal validAfter,
    projection_slot tree location protections position query converted equal valid]
  dsimp only [materialized]
  rw [GeneralBorrowFreshLocation.get_other location.perms index query state different,
    old_default tree index parent query parentNode newNode atEnd parentPresent different]

/-- The fresh index projects to the actual newly inserted state. -/
theorem state_new (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (location : LocationTree) (state : LocationState) (protections : ProtectedTags) :
    (source_normal_projection (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode)
      (materialized location index state) protections).stateAt index.toNat = some state := by
  have valid : index.toNat < (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode).nodes.data.size := by
    rw [attached_size tree index parent parentNode newNode atEnd parentPresent]
    omega
  rw [projection_slot _ _ _ index.toNat index (index_self index) rfl valid]
  dsimp only [materialized]
  rw [GeneralBorrowFreshLocation.get_same]
  rfl

/-- Existing nodes retain exactly their original protector membership. -/
theorem protection_old (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (oldLocation newLocation : LocationTree) (protections : ProtectedTags)
    (position : Nat) (valid : position < tree.nodes.data.size) :
    (source_normal_projection (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode) newLocation protections).protectedNodes.contains position =
      (source_normal_projection tree oldLocation protections).protectedNodes.contains position := by
  rw [protections_exact tree index parent parentNode newNode atEnd parentPresent oldLocation newLocation protections]
  have different : position ≠ index.toNat := by omega
  cases held : protections.contains newNode.tag <;> simp [held,List.contains_append,different,Ne.symm different]

end DuplicatePrefix.GeneralBorrowFreshMaterialization
#print axioms DuplicatePrefix.GeneralBorrowFreshMaterialization.protections_exact
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshMaterialization." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved child materialization dependency {dependency}"
