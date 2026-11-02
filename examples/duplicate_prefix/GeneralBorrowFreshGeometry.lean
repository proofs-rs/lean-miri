import duplicate_prefix.GeneralBorrowFreshRangeFrame
import duplicate_prefix.GeneralBorrowFreshMixedShape
namespace DuplicatePrefix.GeneralBorrowFreshGeometry
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowView
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

theorem ranges_frame (before after : DedupRangeMap α)
    (same : after.entries.map (·.range) = before.entries.map (·.range))
    (well : before.WellFormed) : after.WellFormed ∧ after.size = before.size := by
  have sizes : after.entries.size = before.entries.size := by
    simpa only [Array.size_map] using congrArg Array.size same
  have rangeAt : ∀ position (valid : position < after.entries.size),
      after.entries[position].range = (before.entries[position]'(by omega)).range := by
    intro position valid
    have cell := congrArg (fun a : Array ByteRange => a[position]?) same
    simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,
      Array.getElem?_eq_getElem (by omega : position < before.entries.size),Option.map_some] at cell
    exact Option.some.inj cell
  refine ⟨?_,?_⟩
  · by_cases empty : before.entries.size = 0
    · simp only [DedupRangeMap.WellFormed,show after.entries.size = 0 by omega,↓reduceDIte]
    · simp only [DedupRangeMap.WellFormed,empty,↓reduceDIte] at well
      simp only [DedupRangeMap.WellFormed,show ¬after.entries.size = 0 by omega,↓reduceDIte]
      refine ⟨?_,?_,?_⟩
      · rw [rangeAt 0 (by omega)]
        exact well.1
      · intro position valid
        rw [rangeAt position valid]
        exact well.2.1 position (by omega)
      · intro position valid
        rw [rangeAt position (by omega),rangeAt (position+1) valid]
        exact well.2.2 position (by omega)
  · rw [size_from_ranges after,same,←size_from_ranges before]

theorem shape_frame (before after : BorrowTree) (same : treeShape after = treeShape before)
    (well : before.locations.WellFormed) : after.locations.WellFormed ∧ after.locations.size = before.locations.size := by
  have entries := congrArg (fun shape => shape.2.2.1) same
  have ranges := congrArg (fun rows => rows.map Prod.fst) entries
  simp only [treeShape,Array.map_map,Function.comp_def] at ranges
  exact ranges_frame before.locations after.locations ranges well

theorem sifa_frame (tree : BorrowTree) (start : UniIndex) (strongest : IdempotentForeignAccess)
    (well : tree.locations.WellFormed) :
    (sourceUpdateSifa tree start strongest).1.locations.WellFormed ∧
      (sourceUpdateSifa tree start strongest).1.locations.size = tree.locations.size :=
  shape_frame tree _ (GeneralBorrowSifaView.preserves tree start strongest) well
end DuplicatePrefix.GeneralBorrowFreshGeometry
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshGeometry." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved geometry dependency {dependency}"
