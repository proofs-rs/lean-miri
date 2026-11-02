import empty_function.InputDraft
namespace EmptyFunction.ProjectedFootprint
open Miri Miri.ABI Miri.Memory Miri.Interpreter
open EmptyFunction.WholeCall EmptyFunction.InputDraft
set_option autoImplicit false

/-- Reindex the fresh backing certificate when span bookkeeping, caller slots
or the validation flag change. Its physical/address observations are retained. -/
def atState (before after : State) (pointer : Pointer (Option Provenance)) (size : Size)
    (footprint : IndirectFootprint before pointer size)
    (memory : after.machine.memory = before.machine.memory)
    (addresses : after.machine.user.addresses = before.machine.user.addresses) :
    IndirectFootprint after pointer size where
  id := footprint.id
  entry := footprint.entry
  live := by rw [memory];exact footprint.live
  base := footprint.base
  relative := footprint.relative
  cached := by rw [addresses];exact footprint.cached
  address := footprint.address
  addressFits := footprint.addressFits
  extent := footprint.extent
  attribution := by simpa only [addresses] using footprint.attribution
end EmptyFunction.ProjectedFootprint
