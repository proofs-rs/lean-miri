import duplicate_prefix.CurrentCallConversionInfoRows

namespace DuplicatePrefix.CurrentCallConversionAddressFrames
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open Miri.Memory.AllocAddresses
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The actual address assignment retains old cached bases on every branch,
including resource errors, reuse acquisition and generated-address prefixes. -/
theorem assign (state : GlobalAddressState) (id : AllocId) (info : Option AllocationAddressInfo)
    (choices : AddressRandomChoices) (hooks : AddressExternalHooks)
    (query : AllocId) (base : BaseAddressEntry)
    (hit : state.baseAddr.find? (fun row=>row.allocId==query)=some base) :
    (state.addrFromAllocId id info choices hooks).state.baseAddr.find? (fun row=>row.allocId==query)=some base := by
  cases cached : state.baseAddr.find? (fun row=>row.allocId==id) with
  | some known =>
    unfold GlobalAddressState.addrFromAllocId
    unfold_internal ".GlobalAddressState.findBase"
    simp only [cached,Option.map_some]
    exact hit
  | none =>
    unfold GlobalAddressState.addrFromAllocId
    unfold_internal ".GlobalAddressState.findBase"
    unfold_internal ".GlobalAddressState.setGeneration"
    simp only [cached,Option.map_none]
    repeat' first
      | exact hit
      | exact CurrentCallConversionCacheFrames.base_preserved _ id _ query base hit
      | split

/-- Real acquisition completion only adds the selected target base. Even an
acquisition error preserves every already cached first-match row. -/
theorem acquire (result : AddressStateResult AddressAssignment) (clock : Except String Unit)
    (query : AllocId) (base : BaseAddressEntry)
    (hit : result.state.baseAddr.find? (fun row=>row.allocId==query)=some base) :
    (GlobalAddressState.completeAcquire result clock).state.baseAddr.find? (fun row=>row.allocId==query)=some base := by
  cases result with
  | mk state outcome =>
    cases outcome with
    | error error => exact hit
    | ok assignment =>
      cases assignment with
      | ready address => exact hit
      | acquireRequired id address pending =>
        cases clock with
        | error error => exact hit
        | ok value =>
          cases value
          unfold GlobalAddressState.completeAcquire
          dsimp only
          split <;> exact CurrentCallConversionCacheFrames.base_preserved state id address query base hit

/-- Compose the two actual low-level source address phases. This is a frame
lemma, not a claim that an error or unsupported branch is successful. -/
theorem complete (state : GlobalAddressState) (id : AllocId) (info : Option AllocationAddressInfo)
    (choices : AddressRandomChoices) (hooks : AddressExternalHooks) (clock : Except String Unit)
    (query : AllocId) (base : BaseAddressEntry)
    (hit : state.baseAddr.find? (fun row=>row.allocId==query)=some base) :
    (GlobalAddressState.completeAcquire (state.addrFromAllocId id info choices hooks) clock).state.baseAddr.find?
      (fun row=>row.allocId==query)=some base :=
  acquire _ clock query base (assign state id info choices hooks query base hit)

end DuplicatePrefix.CurrentCallConversionAddressFrames
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallConversionAddressFrames" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual converter address-frame dependency {dependency}"
