import empty_function.Preservation
import empty_function.TreeRuntimeInput

/-! Old observable rights of the zero-byte wildcard root constructor. -/
namespace EmptyFunction.WildcardRights
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowTree.ZeroProtection
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] UniValMap.insert UniValMap.get BorrowTree.newChild
private theorem inserted_mapping (tree : BorrowTree) (tag : BorTag)
    (mapping : UniKeyMap BorTag) (index : UniIndex)
    (fresh : tree.tagMapping.get tag = none)
    (inserted : tree.tagMapping.insert tag = .Inserted mapping index) :
    mapping.mapping = (tree.tagMapping.mapping.filter (fun row => row.1 != tag)).push (tag,index) := by
  cases available : tree.tagMapping.deassigned.back? with
  | some free =>
    simp [UniKeyMap.insert,available,fresh] at inserted
    rcases inserted with ⟨rfl,rfl⟩
    rfl
  | none =>
    cases generated : UniIndex.ofNat? tree.tagMapping.mapping.size with
    | none => simp [UniKeyMap.insert,available,generated] at inserted
    | some free =>
      simp [UniKeyMap.insert,available,generated,fresh] at inserted
      rcases inserted with ⟨rfl,rfl⟩
      rfl

private theorem mapping_old (tree : BorrowTree) (tag : BorTag)
    (mapping : UniKeyMap BorTag) (index : UniIndex)
    (fresh : tree.tagMapping.get tag = none)
    (inserted : tree.tagMapping.insert tag = .Inserted mapping index)
    (oldTag : BorTag) (oldIndex : UniIndex) (old : tree.tagMapping.get oldTag = some oldIndex) :
    mapping.get oldTag = some oldIndex := by
  have different : tag ≠ oldTag := by intro same; subst oldTag; rw [fresh] at old; contradiction
  have filter : tree.tagMapping.mapping.filter (fun row => row.1 != tag) = tree.tagMapping.mapping := by
    apply Array.filter_eq_self.mpr
    intro row member
    have noFind : tree.tagMapping.mapping.find? (fun row => row.1 == tag) = none := by
      unfold UniKeyMap.get at fresh
      cases found : tree.tagMapping.mapping.find? (fun row => row.1 == tag) with
      | none => rfl
      | some foundRow => simp [found] at fresh
    have noMatch := Array.find?_eq_none.mp noFind row member
    simpa only [Bool.not_eq_true,beq_iff_eq,bne_iff_ne] using noMatch
  have data := inserted_mapping tree tag mapping index fresh inserted
  unfold UniKeyMap.get
  rw [data,filter]
  simpa [UniKeyMap.get,Array.find?_push,different] using old


theorem constructor (tree : BorrowTree) (tag : BorTag) (formed : EmptyFunction.TreeRuntimeInput.TreeFormed tree tag)
    (room : tree.tagMapping.mapping.size ≤ 4294967295) (offset : Size) (initial : LocationState) :
    EmptyFunction.Preservation.OldNodeRights tree
      (tree.newChild offset .wildcard tag (DataStructures.DedupRangeMap.new Size.ZERO initial)
        (.ReservedFrz false) true).tree := by
  obtain ⟨mapping,index,inserted,_,vacant⟩ := formed.allocate room
  rw [Release.wildcard_zero_eq tree tag index mapping inserted offset initial]
  dsimp only
  refine ⟨fun oldTag oldIndex old => mapping_old tree tag mapping index formed.nextFresh inserted oldTag oldIndex old,
    fun root member => Array.mem_push_of_mem index member,?_⟩
  intro query old oldAt
  have different : query ≠ index := by intro same;subst query;rw [vacant] at oldAt;contradiction
  refine ⟨old,?_,rfl,rfl,rfl,rfl,rfl,fun child member => member,?_⟩
  · rw [Sparse.get_other tree.nodes index query _ different]
    exact oldAt
  · intro byte segment member contains
    exact ⟨segment,member,contains,rfl,rfl⟩

end EmptyFunction.WildcardRights

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.WildcardRights.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved wildcard-rights axiom: {name}: {dependency}"

namespace EmptyFunction.WildcardRights
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowTree.ZeroProtection
set_option autoImplicit false
/-- Wildcard zero-child old rights need the observed successful insertion,
not an initial u32 room condition. -/
theorem constructor_of_insert (tree : BorrowTree) (tag : BorTag)
    (mapping : UniKeyMap BorTag) (index : UniIndex)
    (fresh : tree.tagMapping.get tag = none)
    (inserted : tree.tagMapping.insert tag = .Inserted mapping index)
    (vacant : tree.nodes.get index = none) (offset : Size) (initial : LocationState) :
    Preservation.OldNodeRights tree
      (tree.newChild offset .wildcard tag (DataStructures.DedupRangeMap.new Size.ZERO initial)
        (.ReservedFrz false) true).tree := by
  rw [Release.wildcard_zero_eq tree tag index mapping inserted offset initial]
  dsimp only
  refine ⟨fun oldTag oldIndex old => mapping_old tree tag mapping index fresh inserted oldTag oldIndex old,
    fun root member => Array.mem_push_of_mem index member,?_⟩
  intro query old oldAt
  have different : query ≠ index := by intro same;subst query;rw [vacant] at oldAt;contradiction
  refine ⟨old,?_,rfl,rfl,rfl,rfl,rfl,fun child member => member,?_⟩
  · rw [Sparse.get_other tree.nodes index query _ different]
    exact oldAt
  · intro byte segment member contains
    exact ⟨segment,member,contains,rfl,rfl⟩
end EmptyFunction.WildcardRights
