import duplicate_prefix.GeneralBorrowConstructorSifaProfile
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutable
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutableReuse
namespace DuplicatePrefix.GeneralBorrowConstructorPriorPermission
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowView DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The earlier tag's stored permission, independently of accessed/SIFA bits. -/
def At (query : UniIndex) (expected : Option Permission) (location : LocationTree) : Prop :=
  (location.perms.get query).map LocationState.permission = expected

/-- Ancestor SIFA updates preserve each prior stored permission at every
physical partition. This does not assume successful SIFA execution. -/
theorem shape (before after : BorrowTree) (same : treeShape after = treeShape before)
    (query : UniIndex) (expected : Option Permission)
    (initial : Every (At query expected) before.locations) :
    Every (At query expected) after.locations := by
  have rows := congrArg (fun row => row.2.2.1) same
  change after.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
    before.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) at rows
  have sizes : after.locations.entries.size = before.locations.entries.size := by
    simpa only [Array.size_map] using congrArg Array.size rows
  intro position valid
  have oldValid : position < before.locations.entries.size := by omega
  have row := congrArg (fun entries => entries[position]?) rows
  simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,
    Array.getElem?_eq_getElem oldValid,Option.map_some] at row
  have locations := (Prod.mk.inj (Option.some.inj row)).2
  have factor (map : UniValMap LocationState) :
      (map.get query).map LocationState.permission =
        ((map.data.map (Option.map stateShape))[query.toNat]?).bind (fun slot => slot.map Prod.fst) := by
    simp only [Array.getElem?_map]
    cases stored : map.data[query.toNat]? with
    | none => simp [UniValMap.get,stored]
    | some state => cases state <;> simp [UniValMap.get,stored,stateShape]
  unfold locationShape at locations
  unfold At at initial ⊢
  rw [factor,locations,←factor]
  exact initial position oldValid

/-- Attaching a later protected child and materializing its range preserves
all earlier stored permissions. In particular a conflict established by its
leading Read cannot be undone by construction. -/
theorem stage (tree : BorrowTree) (index parent query : UniIndex) (parentNode newNode : TreeNode)
    (inside : LocationState) (mapping : UniKeyMap BorTag) (expected : Option Permission)
    (different : query ≠ index) (offset len : UInt64) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (initial : Every (At query expected) tree.locations) (strongest : IdempotentForeignAccess) :
    let staged := GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode newNode mapping
      (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
        (fun _ location => GeneralBorrowFreshMaterialization.materialized location index inside)).state
    Every (At query expected) (sourceUpdateSifa staged parent strongest).1.locations := by
  dsimp only
  apply shape _ _ (GeneralBorrowSifaView.preserves _ parent strongest)
  apply GeneralBorrowExposureChildAttach.modify_every (At query expected) tree.locations
    (Size.ofBytes offset) (Size.ofBytes len) _ well bounds initial
  intro range location good
  change ((location.perms.insert index inside).get query).map LocationState.permission = expected
  rw [GeneralBorrowFreshLocation.get_other _ index query _ different]
  exact good

/-- Actual protected Default append preserves any earlier tag's stored
permission throughout the allocation, including an earlier established conflict. -/
theorem protected_append (input : GeneralBorrowFreshMetadataChildMutable.Input)
    (query : UniIndex) (expected : Option Permission)
    (different : query ≠ GeneralBorrowFreshMetadataChildMutable.index input)
    (initial : Every (At query expected) input.tree.locations) :
    (input.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).outcome = .ok () ∧
    Every (At query expected) (GeneralBorrowFreshMetadataChildMutable.result input).locations := by
  refine ⟨(GeneralBorrowFreshMetadataChildMutable.append input).success,?_⟩
  rw [GeneralBorrowFreshMetadataChildMutable.tree_eq]
  exact stage input.tree (GeneralBorrowFreshMetadataChildMutable.index input) input.parent query input.parentNode
    (GeneralBorrowFreshChild.child input.newTag input.parent) GeneralBorrowFreshChild.inside
    (GeneralBorrowFreshMetadataChildMutable.mapping input) expected different input.offset input.len input.well input.bounds initial .None

/-- Actual protected Default reuse preserves any earlier tag's stored
permission throughout the allocation, including an earlier established conflict. -/
theorem protected_reuse (input : GeneralBorrowFreshMetadataChildMutableReuse.Input)
    (query : UniIndex) (expected : Option Permission)
    (different : query ≠ GeneralBorrowFreshMetadataChildMutableReuse.index input)
    (initial : Every (At query expected) input.tree.locations) :
    (input.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).outcome = .ok () ∧
    Every (At query expected) (GeneralBorrowFreshMetadataChildMutableReuse.result input).locations := by
  refine ⟨(GeneralBorrowFreshMetadataChildMutableReuse.reuse input).success,?_⟩
  rw [GeneralBorrowFreshMetadataChildMutableReuse.tree_eq]
  exact stage input.tree (GeneralBorrowFreshMetadataChildMutableReuse.index input) input.parent query input.parentNode
    (GeneralBorrowFreshChild.child input.newTag input.parent) GeneralBorrowFreshChild.inside
    (GeneralBorrowFreshMetadataChildMutableReuse.mapping input) expected different input.offset input.len input.well input.bounds initial .None

end DuplicatePrefix.GeneralBorrowConstructorPriorPermission
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowConstructorPriorPermission.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved prior constructor permission dependency {dependency}"
