import duplicate_prefix.S05ZeroCellActualCallInit
import duplicate_prefix.PositiveRootInstalledFrame
import duplicate_prefix.GenericFunctionEntryPrefix

/-! Derived frame resources for the fixed installed call. These are phase
outputs of actual initialization, not a caller-validity predicate. -/
namespace DuplicatePrefix.S05ZeroCellActualCallRootFields
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open S05ZeroCellActualCallParameters S05ZeroCellJointPacket
open S05ZeroCellTypedGeneratedPrefix (tag)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

def raw := RawRootInvocation.root before place profile.2.2.2.1
def adjusted (span : PreparedContracts.FixedSpanQuery) :=
  (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
    (Pointer.new (.concrete sourceId (tag 8)) (Size.ofBytes 4096)) 2 ActualReferenceMetadata.reference).imm
def initialFrame (span : PreparedContracts.FixedSpanQuery) :=
  PositiveRootInstalledFrame.installed raw (adjusted span) 1 {} sourceId (tag 8) destinationId (tag 9)

theorem installed_frame (span : PreparedContracts.FixedSpanQuery) (updated : Allocation Provenance BorrowTree) :
    (S05ZeroCellActualCallInit.installed span updated).stack.frames[0]'(by change 0 < 1;decide) = initialFrame span := rfl

set_option autoImplicit false in
structure Facts (original : CompilerFrameContext.ActualFrame) : Prop where
  body : original.body = RootBody.reflected.body.body
  identity : original.bodyIdentity = RootBody.reflected.body.identity
  callee : original.functionInstance = RootBody.reflected.functionInstance
  noClocks : original.extra.dataRace = none
  relevance : original.extra.userRelevance > 0
  tracked : original.extra.borrowTracker = some
    ((({} : FrameState).addProtector sourceId (tag 8)).addProtector destinationId (tag 9))
  destination : original.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩
  continuation : original.returnContinuation = .stop true
  varargs : original.vaList = #[]
  trackNone : original.trackCallerArg = none
  zero : original.locals[0]? = some ⟨.live (.immediate .uninit),none⟩
  count : original.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 1)))),some RootCompilerFacts.usizeLayout⟩
  unused : ∀ index,17 ≤ index → index ≤ 24 → original.locals[index]? = some ⟨.dead,none⟩

/-- Every existing entry-prefix frame shape carries the fixed root resources
needed by the actual copy entry and physical return. -/
theorem of_shape (span : PreparedContracts.FixedSpanQuery) (updated : Allocation Provenance BorrowTree)
    (original : CompilerFrameContext.ActualFrame)
    (shape : GenericFunctionEntryPrefix.Shape
      ((S05ZeroCellActualCallInit.installed span updated).stack.frames[0]'(by change 0 < 1;decide)) original 1) :
    Facts original := by
  rw [installed_frame] at shape
  obtain ⟨body,identity,callee,continuation,destination,varargs,noClocks,tracked,_⟩ :=
    PositiveRootInstalledFrame.metadata raw (adjusted span) 1 {} sourceId (tag 8) destinationId (tag 9)
  have slot (index : Fin 25) := PositiveRootInstalledFrame.slot_option raw
    (RawRootInvocation.locals before place profile.2.2.2.1) (adjusted span) 1 {} sourceId (tag 8) destinationId (tag 9) index
  refine ⟨shape.body.trans (body.trans raw.body),shape.identity.trans (identity.trans raw.identity),
    shape.callee.trans (callee.trans raw.callee),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [shape.extra];exact noClocks.trans raw.noClocks
  · rw [shape.extra]
    rw [initialFrame,PositiveRootInstalledFrame.relevance,raw,PositiveRootInstalledFrame.raw_relevance]
    decide
  · rw [shape.extra];exact tracked
  · rw [shape.returnPlace,initialFrame,destination];rfl
  · exact shape.continuation.trans (continuation.trans rfl)
  · exact shape.vaList.trans (varargs.trans rfl)
  · rw [shape.track]
    exact (PositiveRootInstalledFrame.track raw (adjusted span) 1 {} sourceId (tag 8) destinationId (tag 9)).trans rfl
  · exact shape.slot0.trans (by simpa [initialFrame] using slot ⟨0,by decide⟩)
  · exact shape.slot2.trans (by simpa [initialFrame] using slot ⟨2,by decide⟩)
  · intro index lower upper
    rw [shape.keep index (by omega)]
    simpa [initialFrame,show ¬14=index by omega,show ¬13=index by omega,
      show ¬6=index by omega,show ¬0=index by omega,show ¬2=index by omega,
      show ¬1=index by omega] using slot ⟨index,by omega⟩

end
end DuplicatePrefix.S05ZeroCellActualCallRootFields
