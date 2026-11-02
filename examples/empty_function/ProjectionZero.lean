import empty_function.ProjectionWrapping
namespace EmptyFunction.ProjectionZero
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

theorem source (s : Static) (metadata : Metadata s) (state : State) (place : MemPlace Provenance) :
    EvalProjectionMachine.memoryOffset (ConcreteProtection.source s).pointers state place Size.ZERO .inbounds .none =
      .ok {place with metadata := .none} := by
  have truncate := ConcreteProtection.source_truncate s metadata.pointerSize place.ptr.offset.bytes
  have zeroWord : Int64.toUInt64 (0 : Int64) = (0 : UInt64) := rfl
  unfold EvalProjectionMachine.memoryOffset projectionMemoryOffset MemPlace.offsetWithMeta
  simp [Size.ZERO,Size.ofBytes,MemPlaceMeta.hasMeta,ptrOffsetInbounds,checkPtrAccessSigned,zero_sized_check_skips_resolution,zeroWord,
    Pointer.wrappingSignedOffset,Pointer.wrappingOffset,truncate,Except.mapError,
    bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
  all_goals rfl
end EmptyFunction.ProjectionZero
