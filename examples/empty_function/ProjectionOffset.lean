import empty_function.FactoryProjection
import empty_function.ProjectionWrapping
namespace EmptyFunction.ProjectionOffset
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

theorem wrapping (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (state : State) (place : MemPlace Provenance) (offset : Size) :
    s.cfg.compiler.memoryOffset () place offset .wrapping .none state =
      .ok {place with ptr := {place.ptr with offset := Size.ofBytes (place.ptr.offset.bytes+offset.bytes)},metadata := .none} state := by
  rw [(FactoryProjection.fields s metadata capacity).memory]
  unfold FactoryProjection.action
  rw [ProjectionWrapping.source s metadata state place offset]

theorem validity_wrapping (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (state : State) (place : MemPlace Provenance) (offset : Size) :
    s.cfg.validity.projection.place.memoryOffset () place offset .wrapping .none state =
      .ok {place with ptr := {place.ptr with offset := Size.ofBytes (place.ptr.offset.bytes+offset.bytes)},metadata := .none} state := by
  rw [(FactoryProjection.fields s metadata capacity).validityMemory]
  exact wrapping s metadata capacity state place offset
end EmptyFunction.ProjectionOffset
