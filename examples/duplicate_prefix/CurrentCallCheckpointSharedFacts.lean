import duplicate_prefix.CurrentCallCheckpointSharedControl

namespace DuplicatePrefix.CurrentCallCheckpointSharedFacts
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows CandidateCurrentJointCall CurrentCallPostEntryCheckpoint
open CanonicalConfigFacts ActualReferenceContext RootReferenceInfo
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

private theorem written_slot (frame : CompilerFrameContext.ActualFrame) (localId : MIR.LocalId)
    (layout : LocalLayout) (valid : localId<frame.locals.size) (value : Immediate Provenance) :
    (ActualLocalCopy.written frame localId layout valid value).locals[localId]?=
      some ⟨.live (.immediate value),some layout⟩ := by
  simp [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout]

private theorem written_other (frame : CompilerFrameContext.ActualFrame) (source dest : MIR.LocalId)
    (layout : LocalLayout) (valid : dest<frame.locals.size) (value : Immediate Provenance) (different : source≠dest) :
    (ActualLocalCopy.written frame dest layout valid value).locals[source]?=frame.locals[source]? := by
  simp [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Ne.symm different]

variable {options remaining span len count place} (checkpoint : Checkpoint options remaining span len count place)
    (frame : CompilerFrameContext.ActualFrame) (shape : GenericFunctionEntryPrefix.Shape checkpoint.frame frame count) (base : UInt64)

def caller : CompilerFrameContext.ActualFrame:=
  CurrentCallCheckpointSharedControl.afterFrame checkpoint frame (by rw [shape.size];decide) base

def readerValue : Immediate Provenance:=
  (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete checkpoint.source.role.backing.id checkpoint.tracker.global.nextPointerTag)
      (Size.ofBytes (base+UInt64.ofNat checkpoint.offset))) len SharedReferenceMetadata.sharedLayout).imm

theorem size : (caller checkpoint frame shape base).locals.size=25:=by
  simpa only [caller,CurrentCallCheckpointSharedControl.afterFrame,CopyHelperSteps.advance,ActualLocalCopy.written,
    LocalPlaces.cachePlaceLayout,Array.size_set] using shape.size

theorem slot12 : (caller checkpoint frame shape base).locals[12]?=
    some ⟨.live (.immediate (readerValue checkpoint base)),some SharedReferenceMetadata.sharedLayout⟩:=
  written_slot frame 12 SharedReferenceMetadata.sharedLayout (by rw [shape.size];decide) (readerValue checkpoint base)

theorem slot11 : (caller checkpoint frame shape base).locals[11]?=some ⟨.live (.immediate .uninit),none⟩:=
  (written_other frame 11 12 SharedReferenceMetadata.sharedLayout (by rw [shape.size];decide)
    (readerValue checkpoint base) (by decide)).trans shape.slot11

theorem other (index : Nat) (different : index≠12) :
    (caller checkpoint frame shape base).locals[index]?=frame.locals[index]? :=
  written_other frame index 12 SharedReferenceMetadata.sharedLayout (by rw [shape.size];decide)
    (readerValue checkpoint base) different

theorem count_slot : (caller checkpoint frame shape base).locals[2]?=
    some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ :=
  (other checkpoint frame shape base 2 (by decide)).trans (shape.slot2.trans checkpoint.countLocal)

theorem body : (caller checkpoint frame shape base).body=RootBody.reflected.body.body := shape.body.trans checkpoint.body
theorem identity : (caller checkpoint frame shape base).bodyIdentity=RootBody.reflected.body.identity := shape.identity.trans checkpoint.identity
theorem callee : (caller checkpoint frame shape base).functionInstance=RootBody.reflected.functionInstance := shape.callee.trans checkpoint.callee
theorem location : (caller checkpoint frame shape base).location=.mir ⟨2,12⟩:=rfl
theorem extra : (caller checkpoint frame shape base).extra=checkpoint.frame.extra := shape.extra
theorem noClocks : (caller checkpoint frame shape base).extra.dataRace=none := by rw [extra checkpoint frame shape base];exact checkpoint.noClocks
theorem destination : (caller checkpoint frame shape base).returnPlace=checkpoint.frame.returnPlace := shape.returnPlace
theorem continuation : (caller checkpoint frame shape base).returnContinuation=.stop true := shape.continuation.trans checkpoint.stop
theorem varargs : (caller checkpoint frame shape base).vaList=#[] := shape.vaList.trans checkpoint.varargs
theorem track : (caller checkpoint frame shape base).trackCallerArg=none := shape.track.trans checkpoint.track

end
end DuplicatePrefix.CurrentCallCheckpointSharedFacts

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointSharedFacts" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved common shared frame dependency {dependency}"
