import duplicate_prefix.GeneralBorrowPhysicalReadable
import duplicate_prefix.GeneralBorrowConstructorSifaProfile
import duplicate_prefix.GeneralBorrowStructuralHistoryRootAuthorityAt
namespace DuplicatePrefix.GeneralBorrowPhysicalReadableConstructor
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPhysicalReadable DuplicatePrefix.GeneralBorrowFreshNode
open DuplicatePrefix.GeneralBorrowNodeUpdate DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowView
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] UniValMap.insert
/-- Real graph attachment forms the new lazy state from initial allocator
vacancy plus physical Clean. Node vacancy alone is not used as Clean. -/
theorem attach (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (present : tree.nodeAt parent = some parentNode)
    (initial : Profile tree location protections)
    (newDefault : GeneralBorrowProtectedReadInvariant.Readable newNode.defaultLocationState (protections.contains newNode.tag)) :
    Profile {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode} location protections := by
  have different : parent ≠ index := by
    intro same
    change tree.nodes.get parent = some parentNode at present
    rw [same,vacant] at present;cases present
  have parentAfter : (tree.nodes.insert index newNode).get parent = some parentNode :=
    (GeneralBorrowFreshLocation.get_other _ index parent _ different).trans present
  refine ⟨?_,?_⟩
  · intro query value found
    by_cases isIndex : query = index
    · subst query
      change ((tree.nodes.insert index newNode).insert parent _).get index = some value at found
      rw [GeneralBorrowFreshLocation.get_other _ parent index _ (Ne.symm different),GeneralBorrowFreshLocation.get_same] at found
      cases found
      simp only [initial.vacant index vacant,Option.getD_none]
      exact newDefault
    · by_cases isParent : query = parent
      · subst query
        change ((tree.nodes.insert index newNode).insert parent _).get parent = some value at found
        rw [GeneralBorrowFreshLocation.get_same] at found
        cases found
        exact initial.present parent parentNode present
      · have original : tree.nodeAt query = some value := by
          change ((tree.nodes.insert index newNode).insert parent _).get query = some value at found
          rw [GeneralBorrowFreshLocation.get_other _ parent query _ isParent,
            GeneralBorrowFreshLocation.get_other _ index query _ isIndex] at found
          exact found
        exact initial.present query value original
  · intro query missing
    have isIndex : query ≠ index := by
      intro same;subst query
      change ((tree.nodes.insert index newNode).insert parent _).get index = none at missing
      rw [GeneralBorrowFreshLocation.get_other _ parent index _ (Ne.symm different),GeneralBorrowFreshLocation.get_same] at missing
      cases missing
    have isParent : query ≠ parent := by
      intro same;subst query
      change ((tree.nodes.insert index newNode).insert parent _).get parent = none at missing
      rw [GeneralBorrowFreshLocation.get_same] at missing;cases missing
    change ((tree.nodes.insert index newNode).insert parent _).get query = none at missing
    rw [GeneralBorrowFreshLocation.get_other _ parent query _ isParent,
      GeneralBorrowFreshLocation.get_other _ index query _ isIndex] at missing
    exact initial.vacant query missing

/-- Actual permission materialization at an existing node preserves the full
physical profile when the inserted state's bound is formed under the actual
protection bit. All other stored/default states and vacancies are framed. -/
theorem materialize (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (index : UniIndex) (node : TreeNode) (present : tree.nodeAt index = some node) (state : LocationState)
    (initial : Profile tree location protections)
    (newState : GeneralBorrowProtectedReadInvariant.Readable state (protections.contains node.tag)) :
    Profile tree {location with perms := location.perms.insert index state} protections := by
  refine ⟨?_,?_⟩
  · intro query value found
    by_cases same : query = index
    · subst query
      have equal : value = node := Option.some.inj (found.symm.trans present)
      subst value
      simp only [GeneralBorrowFreshLocation.get_same,Option.getD_some]
      exact newState
    · simpa only [GeneralBorrowFreshLocation.get_other _ index query _ same] using initial.present query value found
  · intro query missing
    have different : query ≠ index := by
      intro same;subst query
      rw [show tree.nodes.get index = some node from present] at missing
      cases missing
    rw [GeneralBorrowFreshLocation.get_other _ index query _ different]
    exact initial.vacant query missing

private theorem allowed_shape (held : Bool) (before after : LocationState)
    (same : stateShape after=stateShape before)
    (allowed : GeneralBorrowProtectedReadInvariant.Readable before held) :
    GeneralBorrowProtectedReadInvariant.Readable after held := by
  rcases before with ⟨oldPermission,oldAccessed,oldSifa⟩
  rcases after with ⟨permission,accessed,sifa⟩
  have equal := Prod.mk.inj same
  change permission=oldPermission ∧ accessed=oldAccessed at equal
  rcases equal with ⟨rfl,rfl⟩
  exact allowed

private theorem mapped_lookup (location : LocationTree) (index : UniIndex) :
    (location.perms.get index).map stateShape=(locationShape location)[index.toNat]?.getD none := by
  unfold UniValMap.get locationShape
  simp only [Array.getElem?_map]
  cases location.perms.data[index.toNat]? <;> rfl

private theorem effective_shape (before after : Option LocationState) (oldDefault newDefault : LocationState)
    (stored : after.map stateShape=before.map stateShape) (defaults : stateShape newDefault=stateShape oldDefault) :
    stateShape (after.getD newDefault)=stateShape (before.getD oldDefault) := by
  cases before <;> cases after <;> simp_all only [Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,Option.some.injEq,reduceCtorEq]

/-- Root authority depends only on permission/accessed data and is transported
through actual SIFA permission views, independently of current protector bits. -/
theorem at_shape (before after : BorrowTree) (oldLocation newLocation : LocationTree) (protections : ProtectedTags)
    (same : treeShape after=treeShape before) (locations : locationShape newLocation=locationShape oldLocation)
    (initial : Profile before oldLocation protections) : Profile after newLocation protections := by
  constructor
  · intro index node present
    obtain ⟨old,found,tagged,_,_,defaultPermission⟩ := GeneralBorrowFreshMetadata.node_fields after before same.symm index node present
    have shapes : (newLocation.perms.get index).map stateShape=(oldLocation.perms.get index).map stateShape := by
      rw [mapped_lookup,locations,←mapped_lookup]
    have defaults : stateShape node.defaultLocationState=stateShape old.defaultLocationState := by
      simp only [stateShape,TreeNode.defaultLocationState]
      rw[defaultPermission]
    rw [←tagged]
    exact allowed_shape _ _ _ (effective_shape _ _ _ _ shapes defaults) (initial.present index old found)
  · intro index missing
    have lookup := GeneralBorrowFreshMetadata.lookup_shape before after same index
    rw [missing,Option.map_none] at lookup
    have oldMissing : before.nodes.get index=none := by
      cases stored : before.nodes.get index with
      | none => rfl
      | some node => simp [stored] at lookup
    have oldClean := initial.vacant index oldMissing
    have shapes : (newLocation.perms.get index).map stateShape=none := by
      rw [mapped_lookup,locations,←mapped_lookup,oldClean]
      rfl
    cases found : newLocation.perms.get index with
    | none => rfl
    | some value => simp [found] at shapes

theorem shape (before after : BorrowTree) (same : treeShape after=treeShape before) (protections : ProtectedTags)
    (initial : Every (fun location=>Profile before location protections) before.locations) :
    Every (fun location=>Profile after location protections) after.locations := by
  have ranges := congrArg (fun value=>value.2.2.1) same
  change after.locations.entries.map (fun segment=>(segment.range,locationShape segment.data))=
    before.locations.entries.map (fun segment=>(segment.range,locationShape segment.data)) at ranges
  have sizes : after.locations.entries.size=before.locations.entries.size := by
    simpa only [Array.size_map] using congrArg Array.size ranges
  intro position valid
  have oldValid : position<before.locations.entries.size := by rw[←sizes];exact valid
  have entries := congrArg (fun entries=>entries[position]?) ranges
  simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,Array.getElem?_eq_getElem oldValid,Option.map_some] at entries
  exact at_shape before after _ _ protections same (congrArg Prod.snd (Option.some.inj entries)) (initial position oldValid)

theorem sifa (tree : BorrowTree) (protections : ProtectedTags) (parent : UniIndex) (minimum : IdempotentForeignAccess)
    (initial : Every (fun location=>Profile tree location protections) tree.locations) :
    Every (fun location=>Profile (sourceUpdateSifa tree parent minimum).1 location protections) (sourceUpdateSifa tree parent minimum).1.locations :=
  shape tree _ (GeneralBorrowSifaView.preserves tree parent minimum) protections initial


end DuplicatePrefix.GeneralBorrowPhysicalReadableConstructor
