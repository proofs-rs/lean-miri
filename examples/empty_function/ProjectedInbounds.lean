import empty_function.IndirectProjection
import empty_function.ProjectionZero
import empty_function.ProjectedFootprint
namespace EmptyFunction.ProjectedInbounds
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.InputDraft
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

theorem source (s : Static) (metadata : Metadata s) (before : State)
    (place : MemPlace Provenance) (id : AllocId) (tag : BorTag)
    (concrete : place.ptr.provenance = some (.concrete id tag)) (length amount : Size)
    (footprint : IndirectFootprint before place.ptr length)
    (within : amount.bytes.toNat ≤ length.bytes.toNat) (signed : length.bytes.toNat < 2^63) :
    EvalProjectionMachine.memoryOffset (ConcreteProtection.source s).pointers before place amount .inbounds .none =
      .ok {place with ptr := {place.ptr with offset := Size.ofBytes (place.ptr.offset.bytes+amount.bytes)},metadata := .none} := by
  by_cases zero : amount.bytes = 0
  · have same : amount = Size.ZERO := by cases amount;cases zero;rfl
    subst amount
    simpa only [Size.ZERO,Size.ofBytes,UInt64.add_zero] using ProjectionZero.source s metadata before place
  · have tables : place.ptr.provenance = some .wildcard → AddressTables before := by
      intro wild
      rw [concrete] at wild
      cases Option.some.inj wild
    exact IndirectProjection.positive s metadata before place length amount footprint tables zero within signed
end EmptyFunction.ProjectedInbounds
