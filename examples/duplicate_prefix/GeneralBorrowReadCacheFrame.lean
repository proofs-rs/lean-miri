import duplicate_prefix.GeneralBorrowFreshActiveOnClean
namespace DuplicatePrefix.GeneralBorrowReadCacheFrame
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshActiveOnClean DuplicatePrefix.GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

open Lean Elab Tactic in
elab "unfold_read_write_scan" : tactic => do
  let found := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".GeneralBorrowRangePreserves.writeScan" then some (mkIdent name) else none
  match found with
  | [name] => evalTactic (← `(tactic| unfold $name:ident))
  | _ => throwError "expected fixed normal materialization scan"

private theorem materialized_cache (location : LocationTree) (states : Array (Option LocationState)) :
    (source_write_states location states).exposedCache = location.exposedCache := by
  unfold_clean_write_states
  simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  change (forIn _ location (source_write_scan states)).exposedCache = location.exposedCache
  have step : ∀ position ∈ List.range' 0 states.size, ∀ current : LocationTree,
      current.exposedCache = location.exposedCache →
      ((source_write_scan states position current).value).exposedCache = location.exposedCache := by
    intro position member current good
    unfold_read_write_scan
    repeat' first | exact good | split
  exact GeneralBorrowLoop.list_invariant _ (source_write_scan states)
    (fun current => current.exposedCache = location.exposedCache) step location rfl

/-- With no exposed node, every actual normal-access cache branch preserves
its input cache, including invalid-index, missing-node and access-error results.
Permissions may still change; no successful-access premise is assumed. -/
theorem normal_cache (tree : BorrowTree) (location : LocationTree) (anchor : UniIndex)
    (kind : AccessKind) (protections : ProtectedTags) (mode : ChildrenVisitMode)
    (unexposed : ∀ index node, tree.nodeAt index = some node → node.isExposed = false) :
    (tree.performNormalAccessAt location anchor kind protections mode).location.exposedCache = location.exposedCache := by
  unfold BorrowTree.performNormalAccessAt
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_normal_cache_scan
  let property := fun state : LocationTree × Except ExposedCacheError Unit => state.1.exposedCache = location.exposedCache
  have step : ∀ event member state, property state → property (scan event member state).value := by
    intro event member state good
    rcases state with ⟨current,outcome⟩
    dsimp only [property] at good ⊢
    cases outcome with
    | error error => simpa only [scan,Bool.false_eq_true,↓reduceIte,ForInStep.value] using good
    | ok unit =>
      cases unit
      cases converted : UniIndex.ofNat? event.node with
      | none => simpa only [scan,converted,Bool.false_eq_true,↓reduceIte,ForInStep.value] using good
      | some index =>
        cases present : tree.nodeAt index with
        | none => simpa only [scan,converted,present,Bool.false_eq_true,↓reduceIte,ForInStep.value] using good
        | some node =>
          simpa only [scan,converted,present,unexposed index node present,Bool.false_and,Bool.false_eq_true,↓reduceIte,ForInStep.value] using good
  have initial : property (source_write_states location
      ((source_normal_projection tree location protections).performAccess anchor.toNat kind mode).tree.locationStates,.ok ()) :=
    materialized_cache location _
  exact GeneralBorrowLoop.list_invariant' _ scan property step _ initial
end DuplicatePrefix.GeneralBorrowReadCacheFrame
