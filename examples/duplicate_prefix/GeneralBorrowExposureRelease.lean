import duplicate_prefix.GeneralBorrowExposure
import duplicate_prefix.GeneralRangeMapState
namespace DuplicatePrefix.GeneralBorrowExposureRelease
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralRangeMapState
open Lean Elab Tactic
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
elab "unfold_source_update_locations" : tactic => do
  let candidates := (← getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".BorrowTree.updateEveryLocation" then some name else none
  match candidates with
  | [name] => let name := mkIdent name; evalTactic (← `(tactic| unfold $name:ident))
  | _ => throwError "expected actual updateEveryLocation"
elab "name_release_exposure_scan" : tactic => do
  liftMetaTactic fun goal => goal.withContext do
    let target ← goal.getType
    let some loop := target.find? (fun expr => expr.isAppOf ``ForIn'.forIn')
      | throwError "expected actual location loop"
    let body := loop.getAppArgs.back!
    let goal ← goal.define `scan (← Lean.Meta.inferType body) body
    let (scan,goal) ← goal.intro1P
    let target ← goal.getType
    return [← goal.change (target.replace fun expr => if expr == body then some (mkFVar scan) else none)]

theorem succeeds (tree : BorrowTree) (tag : BorTag) (index : UniIndex) (node : TreeNode)
    (tagged : tree.indexOfTag tag = some index) (present : tree.nodeAt index = some node)
    (depth : ParentDepth tree.nodes) :
    (tree.updateExposureForProtectorRelease tag).outcome = .ok () := by
  unfold BorrowTree.updateExposureForProtectorRelease
  simp only [tagged,present,Id.run,pure]
  split
  · rfl
  · unfold_source_update_locations
    simp only [Id.run,bind,pure,ForIn.forIn,Std.Legacy.Range.forIn'_eq_forIn'_range',Std.Legacy.Range.size]
    name_release_exposure_scan
    let property := fun state : Option BorrowTree.TreeMutationResult × BorrowTree =>
      state.1 = none ∧ state.2.nodes = tree.nodes ∧ state.2.locations.entries.size = tree.locations.entries.size
    have step : ∀ position member state, property state → property (scan position member state).value := by
      intro position member state good
      rcases state with ⟨returned,current⟩
      rcases good with ⟨returnedEq,nodesEq,lengthEq⟩
      dsimp only at returnedEq nodesEq lengthEq
      subst returned
      have positionBound : position < tree.locations.entries.size := by
        have bounded := List.mem_range'_1.mp member
        simpa using bounded.2
      have valid : position < current.locations.entries.size := by rw [lengthEq]; exact positionBound
      let location := current.locations.entries[position].data
      let oldState := (location.perms.get index).getD node.defaultLocationState
      let wasAllowed := oldState.permission.strongestAllowedLocalAccess true
      let nowAllowed := oldState.permission.strongestAllowedLocalAccess false
      let update := location.exposedCache.updateExposure tree.nodes index wasAllowed nowAllowed
      let nextLocation := {location with exposedCache := update.cache}
      let nextTree := {current with locations := (current.locations.setAtPos position nextLocation).state}
      have cacheOK : update.outcome = .ok () := update_exposure_succeeds location.exposedCache tree.nodes depth index node present wasAllowed nowAllowed
      have actual : scan position member (none,current) = .yield (none,nextTree) := by
        simp only [scan,index_exact current.locations position valid]
        dsimp only [location,oldState,wasAllowed,nowAllowed,update] at cacheOK
        simp only [cacheOK,setAtPos_success current.locations position valid]
        rfl
      rw [actual]
      refine ⟨rfl,nodesEq,?_⟩
      exact (setAtPos_length current.locations position valid nextLocation).trans lengthEq
    have initial : property (none,tree) := ⟨rfl,rfl,rfl⟩
    have maintained := GeneralBorrowLoop.list_invariant' _ scan property step _ initial
    rw [maintained.1]
end DuplicatePrefix.GeneralBorrowExposureRelease

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowExposureRelease." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved generic protector exposure dependency {dependency}"
