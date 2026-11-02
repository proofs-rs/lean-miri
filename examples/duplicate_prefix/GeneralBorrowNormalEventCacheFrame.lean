import duplicate_prefix.GeneralBorrowReadCacheFrame
namespace DuplicatePrefix.GeneralBorrowNormalEventCacheFrame
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshActiveOnClean DuplicatePrefix.GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

open Lean Elab Term in
elab "checked_materialized_cache" : term => do
  let found := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".GeneralBorrowReadCacheFrame.materialized_cache" then some name else none
  match found with
  | [name] => return mkConst name
  | _ => throwError "expected checked normal materialization cache theorem"

/-- Only nodes in the actual normal-access event list need be unexposed.
Exposed nodes elsewhere in the allocation impose no premise. Invalid indices,
missing nodes, failed accesses and prior cache errors retain their source results. -/
theorem normal_cache (tree : BorrowTree) (location : LocationTree) (anchor : UniIndex)
    (kind : AccessKind) (protections : ProtectedTags) (mode : ChildrenVisitMode)
    (unexposed : ∀ event ∈ ((source_normal_projection tree location protections).performAccess
        anchor.toNat kind mode).visited, ∀ index node,
      UniIndex.ofNat? event.node = some index → tree.nodeAt index = some node → node.isExposed = false) :
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
          have flag := unexposed event member index node converted present
          simpa only [scan,converted,present,flag,Bool.false_and,Bool.false_eq_true,↓reduceIte,ForInStep.value] using good
  have initial : property (source_write_states location
      ((source_normal_projection tree location protections).performAccess anchor.toNat kind mode).tree.locationStates,.ok ()) :=
    checked_materialized_cache location _
  exact GeneralBorrowLoop.list_invariant' _ scan property step _ initial
end DuplicatePrefix.GeneralBorrowNormalEventCacheFrame
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowNormalEventCacheFrame." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved event-local cache frame dependency {dependency}"
