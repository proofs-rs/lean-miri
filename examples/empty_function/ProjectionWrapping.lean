import empty_function.ConcreteProtection
namespace EmptyFunction.ProjectionWrapping
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

theorem source (s : Static) (metadata : Metadata s) (state : State) (place : MemPlace Provenance) (offset : Size) :
    EvalProjectionMachine.memoryOffset (ConcreteProtection.source s).pointers state place offset .wrapping .none =
      .ok {place with ptr := {place.ptr with offset := Size.ofBytes (place.ptr.offset.bytes+offset.bytes)},metadata := .none} := by
  have truncated := ConcreteProtection.source_truncate s metadata.pointerSize (place.ptr.offset.bytes+offset.bytes)
  unfold EvalProjectionMachine.memoryOffset projectionMemoryOffset MemPlace.offsetWithMeta
  simp [MemPlaceMeta.hasMeta,Except.mapError,Pointer.wrappingOffset,truncated,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
end EmptyFunction.ProjectionWrapping
