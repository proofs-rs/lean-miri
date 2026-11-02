import empty_function.Specification
namespace EmptyFunction.ProtectionPlace
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open EmptyFunction.WholeCall
/-- Facts about the evaluated unit memory place. It need not be represented as
`Packet.destination`: local destinations retain their original return place. -/
structure Input (s : Static) (before : State) (tracker : MachineHooks.BorrowState) where
  place : MPlaceTy Provenance
  layout : place.layout = s.abi.ret.layout
  sizedMetadata : place.mplace.metadata = .none
  alignmentCache : place.mplace.misaligned = none
  pointer : InputDraft.PointerInput s before tracker place.mplace.ptr
end EmptyFunction.ProtectionPlace
