import duplicate_prefix.GeneralBorrowFreshFrozenFormation
namespace DuplicatePrefix.GeneralBorrowFreshFutureClean
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowView
open DuplicatePrefix.GeneralBorrowFreshMaterialization
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def Clean (tree : BorrowTree) (query : UniIndex) : Prop :=
  Every (fun location : LocationTree => location.perms.get query = none) tree.locations

/-- Installing the first child at another index leaves a future child's slot
clean throughout the allocation. Range preparation and callback iteration are
actual operations; their success is not an input assumption. -/
theorem modified (map : DedupRangeMap LocationTree) (index query : UniIndex) (offset len : Size) (state : LocationState)
    (different : query ≠ index) (well : map.WellFormed) (bounds : offset.bytes.toNat+len.bytes.toNat ≤ map.size.bytes.toNat)
    (clean : Every (fun location : LocationTree => location.perms.get query = none) map) :
    Every (fun location : LocationTree => location.perms.get query = none)
      (map.modifyRange offset len (fun _ location => materialized location index state)).state := by
  have prepared := GeneralRangeMapSafety.iter_mut (fun location : LocationTree => location.perms.get query = none)
    map offset len well clean bounds
  rw [GeneralBorrowFreshModify.state_exact map offset len _ well bounds]
  have fold : ∀ (positions : List Nat) (current : DedupRangeMap LocationTree),
      Every (fun location : LocationTree => location.perms.get query = none) current →
      Every (fun location : LocationTree => location.perms.get query = none)
        (positions.foldl (fun current position => GeneralBorrowFreshModify.atPosition current position
          (fun _ location => materialized location index state)) current) := by
    intro positions
    induction positions with
    | nil => intro current all;exact all
    | cons position rest ih =>
      intro current all
      apply ih
      dsimp only [GeneralBorrowFreshModify.atPosition]
      split
      · rename_i valid
        apply replaced_every _ current position valid _ all
        dsimp only [materialized]
        rw [GeneralBorrowFreshLocation.get_other _ index query state different]
        exact all position valid
      · exact all
  exact fold _ _ prepared.every

private theorem get_map {α β : Type} (shape : α → β) (nodes : UniValMap α) (query : UniIndex) :
    (⟨nodes.data.map (Option.map shape)⟩ : UniValMap β).get query = (nodes.get query).map shape := by
  unfold UniValMap.get
  simp only [Array.getElem?_map]
  cases cell : nodes.data[query.toNat]? with
  | none => rfl
  | some entry => cases entry <;> rfl

theorem shape_preserves (before after : BorrowTree) (same : treeShape after = treeShape before)
    (query : UniIndex) (clean : Clean before query) : Clean after query := by
  have ranges := congrArg (fun row => row.2.2.1) same
  change after.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
    before.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) at ranges
  have sizes : after.locations.entries.size = before.locations.entries.size := by
    have known := congrArg Array.size ranges
    simpa only [Array.size_map] using known
  intro position valid
  have oldValid : position < before.locations.entries.size := by rw [←sizes];exact valid
  have shapes : locationShape after.locations.entries[position].data = locationShape before.locations.entries[position].data := by
    have known := congrArg (fun rows => rows[position]?) ranges
    simp only [Array.getElem?_map,Array.getElem?_eq_getElem (xs := after.locations.entries) (i := position) valid,
      Array.getElem?_eq_getElem (xs := before.locations.entries) (i := position) oldValid,Option.map_some] at known
    exact (Prod.mk.inj (Option.some.inj known)).2
  have lookups := congrArg (fun data => (⟨data⟩ : UniValMap StateShape).get query) shapes
  dsimp only [locationShape] at lookups
  rw [get_map,get_map,clean position oldValid] at lookups
  cases stored : after.locations.entries[position].data.perms.get query with
  | none => rfl
  | some state => simp only [stored,Option.map_some,Option.map_none] at lookups;cases lookups

theorem sifa_preserves (tree : BorrowTree) (start : UniIndex) (strongest : IdempotentForeignAccess)
    (query : UniIndex) (clean : Clean tree query) : Clean (sourceUpdateSifa tree start strongest).1 query := by
  exact shape_preserves tree _ (GeneralBorrowSifaView.preserves tree start strongest) query clean
end DuplicatePrefix.GeneralBorrowFreshFutureClean
