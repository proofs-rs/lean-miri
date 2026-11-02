import duplicate_prefix.GeneralBorrowRawRootPrefixResources
namespace DuplicatePrefix.GeneralBorrowRawRootPrefixFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GenericFunctionEntryState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
abbrev Initial := GeneralBorrowRawRootZeroEntry.Initial

def sourceValue (s : Initial) : Immediate Provenance :=
  (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
    (Pointer.new (.concrete s.id s.tracker.global.nextPointerTag) (Size.ofBytes (s.base+s.offset)))
    s.len ActualReferenceMetadata.reference).imm

structure Facts (s : Initial) (n : UInt64) (frame : CompilerFrameContext.ActualFrame) : Prop where
  body : frame.body = RootBody.reflected.body.body
  identity : frame.bodyIdentity = RootBody.reflected.body.identity
  callee : frame.functionInstance = RootBody.reflected.functionInstance
  location : frame.location = .mir ⟨2,11⟩
  size : frame.locals.size = 25
  clocks : frame.extra.dataRace = none
  source : frame.locals[1]? = some ⟨.live (.immediate (sourceValue s)),some ActualReferenceMetadata.reference⟩
  dest : frame.locals[12]? = some ⟨.live (.immediate .uninit),none⟩
  len : frame.locals[11]? = some ⟨.live (.immediate .uninit),none⟩
  count : frame.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩

/-- All physical facts at the shared Ref site come from the fixed initializer
and actual pure-prefix shape. No future frame or metadata premise is required. -/
theorem of_shape (s : Initial) (n : UInt64) (entry frame : CompilerFrameContext.ActualFrame)
    (initial : entry = GeneralBorrowRawRootInitialize.caller s n)
    (shape : GenericFunctionEntryPrefix.Shape entry frame n) : Facts s n frame := by
  let raw := RawRootInvocation.root s.before s.place s.race
  let adjusted := sourceValue s
  let installed := PositiveRootInstalledFrame.installed raw adjusted n {} s.id s.tracker.global.nextPointerTag s.slotId
    (next s.tracker s.fresh).global.nextPointerTag
  have fixed : entry = installed := initial
  obtain ⟨body,identity,callee,continuation,place,varargs,clocks,borrow,location⟩ :=
    PositiveRootInstalledFrame.metadata raw adjusted n {} s.id s.tracker.global.nextPointerTag s.slotId
      (next s.tracker s.fresh).global.nextPointerTag
  have slots (i : Fin 25) := PositiveRootInstalledFrame.slot_option raw (RawRootInvocation.locals s.before s.place s.race)
    adjusted n {} s.id s.tracker.global.nextPointerTag s.slotId (next s.tracker s.fresh).global.nextPointerTag i
  refine ⟨?_,?_,?_,shape.location,shape.size,?_,?_,shape.slot12,shape.slot11,?_⟩
  · rw [shape.body,fixed,body];exact raw.body
  · rw [shape.identity,fixed,identity];exact raw.identity
  · rw [shape.callee,fixed,callee];exact raw.callee
  · rw [shape.extra,fixed,clocks];exact raw.noClocks
  · rw [shape.slot1,fixed]
    simpa only [Nat.reduceEqDiff,or_self,ite_false,ite_true] using slots ⟨1,by decide⟩
  · rw [shape.slot2,fixed]
    simpa only [Nat.reduceEqDiff,or_self,ite_false,ite_true] using slots ⟨2,by decide⟩
end
end DuplicatePrefix.GeneralBorrowRawRootPrefixFrame
