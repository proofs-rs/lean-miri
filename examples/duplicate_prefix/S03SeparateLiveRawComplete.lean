import duplicate_prefix.S03SeparateLiveRawInstalledPacket
import duplicate_prefix.S03SeparateLivePacketComplete
import duplicate_prefix.SuccessfulTraceTerminal

namespace DuplicatePrefix.S03SeparateLiveRawComplete
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- The original every-count Result from the local INITIAL packet used by
lazy-image preparation. This does not ask for a new whole-call work budget on
the materialized memory or for a prepared Contract. -/
theorem complete
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (s : S03SeparateLiveRawInstalledPacket.Initial options limits remaining span before pointer place)
    (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer pointer) 0 count place := by
  obtain ⟨frame,machine,entry,⟨packet⟩⟩ := S03SeparateLiveRawInstalledPacket.enters s count
  obtain ⟨done,trace,terminal,empty,noErrors,noUb⟩ := S03SeparateLivePacketComplete.complete options limits remaining span frame machine place
    pointer.offset.bytes count packet s.nonnull s.validityFuel s.dynamicFuel s.budget s.dynamicEq s.dispatchEq
    s.model.preciseOff s.model.implicitOff s.model.nullComparator s.model.debugOff s.validityEq
    (DuplicatePrefixCallModel.sourceComparator _ _ _ _ s.model)
  exact ⟨Storage.withCurrent #[] frame machine,done,entry,trace,terminal,empty,noErrors,noUb,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

end
end DuplicatePrefix.S03SeparateLiveRawComplete
