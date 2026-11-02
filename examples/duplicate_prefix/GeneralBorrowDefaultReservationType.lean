import duplicate_prefix.GeneralBorrowDefaultInvariant
import duplicate_prefix.GeneralBorrowWriteActivationUnique
namespace DuplicatePrefix.GeneralBorrowDefaultReservationType
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowView
open DuplicatePrefix.GeneralBorrowFreshMaterialization DuplicatePrefix.GeneralBorrowFreshInstallation
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def Reserved (state : LocationState) : Prop := state.permission = .ReservedFrz false
def LocationTyped (location : LocationTree) (query : UniIndex) : Prop :=
  ∀ state, location.perms.get query = some state → Reserved state
def DefaultTyped (tree : BorrowTree) (query : UniIndex) : Prop :=
  ∀ node, tree.nodeAt query = some node → node.defaultInitialPermission = .ReservedFrz false
def TreeTyped (tree : BorrowTree) (query : UniIndex) : Prop :=
  DefaultTyped tree query ∧ Every (fun location => LocationTyped location query) tree.locations

theorem clean_typed (map : DedupRangeMap LocationTree) (query : UniIndex)
    (clean : Every (fun location : LocationTree => location.perms.get query = none) map) :
    Every (fun location => LocationTyped location query) map := by
  intro position valid state stored
  rw [clean position valid] at stored
  cases stored

theorem materialized_typed (location : LocationTree) (query : UniIndex) (inserted : LocationState)
    (typed : Reserved inserted) : LocationTyped (materialized location query inserted) query := by
  intro state present
  dsimp only [materialized] at present
  rw [GeneralBorrowFreshLocation.get_same] at present
  have same : inserted = state := Option.some.inj present
  subst state
  exact typed

/-- A real range insertion of a Reserved/Disabled state preserves stored typing;
preparation, splitting and equal-value merging retain the original typing. -/
theorem modified (map : DedupRangeMap LocationTree) (query : UniIndex) (offset len : Size) (inserted : LocationState)
    (well : map.WellFormed) (bounds : offset.bytes.toNat+len.bytes.toNat ≤ map.size.bytes.toNat)
    (before : Every (fun location => LocationTyped location query) map) (typed : Reserved inserted) :
    Every (fun location => LocationTyped location query)
      (map.modifyRange offset len (fun _ location => materialized location query inserted)).state := by
  have prepared := GeneralRangeMapSafety.iter_mut (fun location => LocationTyped location query) map offset len well before bounds
  rw [GeneralBorrowFreshModify.state_exact map offset len _ well bounds]
  have fold : ∀ (positions : List Nat) (current : DedupRangeMap LocationTree),
      Every (fun location => LocationTyped location query) current →
      Every (fun location => LocationTyped location query)
        (positions.foldl (fun current position => GeneralBorrowFreshModify.atPosition current position
          (fun _ location => materialized location query inserted)) current) := by
    intro positions
    induction positions with
    | nil => intro current all;exact all
    | cons position rest ih =>
      intro current all
      apply ih
      dsimp only [GeneralBorrowFreshModify.atPosition]
      split
      · rename_i valid
        exact replaced_every _ current position valid _ all (materialized_typed _ query inserted typed)
      · exact all
  exact fold _ _ prepared.every

private theorem get_map {α β : Type} (shape : α → β) (nodes : UniValMap α) (query : UniIndex) :
    (⟨nodes.data.map (Option.map shape)⟩ : UniValMap β).get query = (nodes.get query).map shape := by
  unfold UniValMap.get
  simp only [Array.getElem?_map]
  cases cell : nodes.data[query.toNat]? with
  | none => rfl
  | some entry => cases entry <;> rfl

/-- SIFA-only shape changes retain both the default and every stored Reserved/
Disabled permission. No successful SIFA outcome is assumed here. -/
theorem shape_preserves (before after : BorrowTree) (same : treeShape after = treeShape before)
    (query : UniIndex) (typed : TreeTyped before query) : TreeTyped after query := by
  have nodes := congrArg (fun row => row.2.1) same
  change after.nodes.data.map (Option.map nodeShape) = before.nodes.data.map (Option.map nodeShape) at nodes
  have nodeLookups := congrArg (fun data => (⟨data⟩ : UniValMap NodeShape).get query) nodes
  rw [get_map,get_map] at nodeLookups
  have ranges := congrArg (fun row => row.2.2.1) same
  change after.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
    before.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) at ranges
  have sizes : after.locations.entries.size = before.locations.entries.size := by
    have known := congrArg Array.size ranges
    simpa only [Array.size_map] using known
  constructor
  · intro node present
    change after.nodes.get query = some node at present
    rw [present] at nodeLookups
    cases old : before.nodes.get query with
    | none => simp only [old,Option.map_none,Option.map_some] at nodeLookups;cases nodeLookups
    | some oldNode =>
      have shapes : nodeShape node = nodeShape oldNode := by simpa only [old,Option.map_some,Option.some.injEq] using nodeLookups
      have permission : node.defaultInitialPermission = oldNode.defaultInitialPermission := congrArg (fun row => row.2.2.2) shapes
      rw [permission]
      exact typed.1 oldNode old
  · intro position valid state stored
    have oldValid : position < before.locations.entries.size := by rw [←sizes];exact valid
    have entryShapes : locationShape after.locations.entries[position].data = locationShape before.locations.entries[position].data := by
      have known := congrArg (fun rows => rows[position]?) ranges
      simp only [Array.getElem?_map,Array.getElem?_eq_getElem (xs := after.locations.entries) (i := position) valid,
        Array.getElem?_eq_getElem (xs := before.locations.entries) (i := position) oldValid,Option.map_some] at known
      exact (Prod.mk.inj (Option.some.inj known)).2
    have lookups := congrArg (fun data => (⟨data⟩ : UniValMap StateShape).get query) entryShapes
    dsimp only [locationShape] at lookups
    rw [get_map,get_map,stored] at lookups
    cases old : before.locations.entries[position].data.perms.get query with
    | none => simp only [old,Option.map_none,Option.map_some] at lookups;cases lookups
    | some oldState =>
      have shapes : stateShape state = stateShape oldState := by simpa only [old,Option.map_some,Option.some.injEq] using lookups
      have permission : state.permission = oldState.permission := congrArg Prod.fst shapes
      simpa only [Reserved,permission] using typed.2 position oldValid oldState old

theorem sifa_preserves (tree : BorrowTree) (start : UniIndex) (strongest : IdempotentForeignAccess)
    (query : UniIndex) (typed : TreeTyped tree query) : TreeTyped (sourceUpdateSifa tree start strongest).1 query := by
  exact shape_preserves tree _ (GeneralBorrowSifaView.preserves tree start strongest) query typed

/-- The source effective state, whether stored or lazy, is reserved. -/
theorem effective (tree : BorrowTree) (location : LocationTree) (query : UniIndex) (node : TreeNode)
    (present : tree.nodeAt query = some node) (default : DefaultTyped tree query)
    (stored : LocationTyped location query) :
    ∀ state, (source_normal_projection tree location {}).stateAt query.toNat = some state → state.permission = .ReservedFrz false := by
  intro state found
  rw [GeneralBorrowProjection.projection_state tree location {} query.toNat query node (GeneralBorrowProjection.index_self query) rfl present] at found
  cases entry : location.perms.get query with
  | none =>
    have same : node.defaultLocationState = state := Option.some.inj (by simpa only [entry,Option.getD_none] using found)
    rw [←same]
    exact default node present
  | some value =>
    have same : value = state := Option.some.inj (by simpa only [entry,Option.getD_some] using found)
    subst value
    exact stored state entry

namespace Append
open GeneralBorrowFreshMetadataChildDefault
/-- The real reservation tree has reserved defaults and stored child states. -/
theorem formed (input : Input)
    (clean : Every (fun location : LocationTree => location.perms.get (index input) = none) input.tree.locations) :
    TreeTyped (result input) (index input) := by
  have typed := modified input.tree.locations (index input) (Size.ofBytes input.offset) (Size.ofBytes input.len)
    GeneralBorrowFreshDefaultChild.inside input.well input.bounds (clean_typed _ _ clean) (by change (Permission.ReservedFrz false) = .ReservedFrz false;decide)
  have freshNode : (stage input).nodeAt (index input) = some (GeneralBorrowFreshDefaultChild.child input.newTag input.parent) := by
    simpa only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt] using
      GeneralBorrowFreshGraph.new_lookup input.tree (index input) input.parent input.parentNode
        (GeneralBorrowFreshDefaultChild.child input.newTag input.parent) (at_end input) input.parentPresent
  apply shape_preserves (stage input) (result input) (shape input) (index input)
  refine ⟨?_,typed⟩
  intro node present
  have same : node = GeneralBorrowFreshDefaultChild.child input.newTag input.parent := Option.some.inj (present.symm.trans freshNode)
  rw [same]
  change (Permission.ReservedFrz false) = .ReservedFrz false
  decide
end Append

namespace Reuse
open GeneralBorrowFreshMetadataChildDefaultReuse

theorem formed (input : Input)
    (clean : Every (fun location : LocationTree => location.perms.get (index input) = none) input.tree.locations) :
    TreeTyped (result input) (index input) := by
  have typed := modified input.tree.locations (index input) (Size.ofBytes input.offset) (Size.ofBytes input.len)
    GeneralBorrowFreshDefaultChild.inside input.well input.bounds (clean_typed _ _ clean) (by change (Permission.ReservedFrz false) = .ReservedFrz false;decide)
  have freshNode : (stage input).nodeAt (index input) = some (GeneralBorrowFreshDefaultChild.child input.newTag input.parent) := by
    simpa only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt,index] using
      GeneralBorrowFreshMetadataChildReuseGraph.new_lookup input.tree input.index input.parent input.parentNode
        (GeneralBorrowFreshDefaultChild.child input.newTag input.parent) input.vacant input.parentPresent
  apply shape_preserves (stage input) (result input) (shape input) (index input)
  refine ⟨?_,typed⟩
  intro node present
  have same : node = GeneralBorrowFreshDefaultChild.child input.newTag input.parent := Option.some.inj (present.symm.trans freshNode)
  rw [same]
  change (Permission.ReservedFrz false) = .ReservedFrz false
  decide
end Reuse
end DuplicatePrefix.GeneralBorrowDefaultReservationType
