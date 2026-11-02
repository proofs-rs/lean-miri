import empty_function.AddressPost
namespace EmptyFunction.AddressBasePost
open Miri Miri.Memory Miri.Memory.AllocAddresses
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private theorem cache_bases (state : GlobalAddressState) (id : AllocId) (address : UInt64)
    (oldId : AllocId) (old : BaseAddressEntry)
    (prior : state.baseAddr.find? (fun row => row.allocId == oldId) = some old) :
    (state.cacheAddress id address).state.baseAddr.find? (fun row => row.allocId == oldId) = some old := by
  unfold GlobalAddressState.cacheAddress
  unfold_source_base
  unfold_source_insert_base
  cases selected : state.baseAddr.find? (fun row => row.allocId == id) with
  | some row => simpa only [selected,Option.map_some,Id.run,pure] using prior
  | none =>
    have noFilter : state.baseAddr.filter (fun row => row.allocId != id) = state.baseAddr := by
      apply Array.filter_eq_self.mpr
      intro row member
      have missing := Array.find?_eq_none.mp selected row member
      simp only [bne,missing,Bool.not_false]
    simp only [selected,Option.map_none,noFilter]
    repeat' first
      | (solve | simp only [Array.find?_push,prior,Option.or,Id.run,pure])
      | split

private theorem assigned_bases (result : AddressStateResult AddressAssignment) (after : GlobalAddressState)
    (actual : AddressChoicePlan.assignedState result = .ok after)
    (id : AllocId) (old : BaseAddressEntry)
    (prior : result.state.baseAddr.find? (fun row => row.allocId == id) = some old) :
    after.baseAddr.find? (fun row => row.allocId == id) = some old := by
  unfold AddressChoicePlan.assignedState at actual
  split at actual
  · cases actual
  · cases actual
    exact prior
  · dsimp only at actual
    split at actual
    · cases actual
    · cases actual
      exact cache_bases _ _ _ id old prior

/-- An actual completed address assignment retains every earlier base-cache
lookup. This covers cache hits, zero TypeId addresses, reuse/acquire and bumps;
it does not require alignment normalization for an already cached target. -/
theorem retained (state : GlobalAddressState) (id : AllocId)
    (info : AllocationAddressInfo) (choices : AddressRandomChoices) (after : GlobalAddressState)
    (actual : AddressChoicePlan.assignedState (state.addrFromAllocId id (some info) choices) = .ok after)
    (oldId : AllocId) (old : BaseAddressEntry)
    (prior : state.baseAddr.find? (fun row => row.allocId == oldId) = some old) :
    after.baseAddr.find? (fun row => row.allocId == oldId) = some old := by
  apply assigned_bases _ after actual oldId old
  unfold GlobalAddressState.addrFromAllocId
  split
  · exact prior
  · simp only
    cases kind : info.memoryKind with
    | none => simpa only [kind,Id.run,pure] using prior
    | some memoryKind =>
      simp only [kind,Id.run,pure]
      split
      · exact prior
      · split
        · split <;> exact cache_bases _ _ _ oldId old prior
        · cases mode : state.addressMode with
          | nativeLib => simpa only [mode,Id.run,pure] using prior
          | managed =>
            simp only [mode,Id.run,pure]
            cases current : state.generation with
            | none => simpa only [current,Id.run,pure] using prior
            | some generation =>
              simp only [current,Id.run,pure]
              split
              · exact prior
              · split
                · exact prior
                · split <;> exact cache_bases _ _ _ oldId old prior
              · split
                · exact prior
                · split <;> exact cache_bases _ _ _ oldId old prior

end EmptyFunction.AddressBasePost
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.AddressBasePost.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved retained address base axiom {dependency} in {name}"
