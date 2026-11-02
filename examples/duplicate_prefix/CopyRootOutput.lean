import duplicate_prefix.CopyCallStep
import duplicate_prefix.PtrMetadataExecution
import duplicate_prefix.CopyHelperCleanup
namespace DuplicatePrefix.CopyRootOutput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable def caller (frame : CompilerFrameContext.ActualFrame) (valid : 18 < frame.locals.size) :=
  let cached := CopyUncachedCall.cachedCaller frame valid
  {PtrMetadataExecution.writeFrame cached 18 .uninit (by simpa [cached,CopyUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout] using valid)
    with location := .mir ⟨9,0⟩}
 theorem slot18 (frame : CompilerFrameContext.ActualFrame) (valid : 18 < frame.locals.size) :
    (caller frame valid).locals[18]'(by simpa [caller,PtrMetadataExecution.writeFrame,CopyUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout] using valid) =
      ⟨.live (.immediate .uninit),some CopyHelperUnit.layout⟩ := by
  simp only [caller,PtrMetadataExecution.writeFrame,CopyUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self]
 theorem metadata (frame : CompilerFrameContext.ActualFrame) (valid : 18 < frame.locals.size) :
    let result := caller frame valid
    result.body = frame.body ∧ result.bodyIdentity = frame.bodyIdentity ∧ result.functionInstance = frame.functionInstance ∧
    result.extra = frame.extra ∧ result.returnContinuation = frame.returnContinuation ∧ result.returnPlace = frame.returnPlace ∧
    result.vaList = frame.vaList ∧ result.trackCallerArg = frame.trackCallerArg ∧ result.localsIdentity = frame.localsIdentity ∧
    result.locals.size = frame.locals.size ∧ result.location = .mir ⟨9,0⟩ := by
  simp only [caller,PtrMetadataExecution.writeFrame,CopyUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.size_set]
  repeat' constructor
 theorem other (frame : CompilerFrameContext.ActualFrame) (valid : 18 < frame.locals.size) (index : Nat)
    (different : index ≠ 18) :
    (caller frame valid).locals[index]? = frame.locals[index]? := by
  simp [caller,PtrMetadataExecution.writeFrame,CopyUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,
    Ne.symm different]
 theorem all_immediate (frame : CompilerFrameContext.ActualFrame) (valid : 18 < frame.locals.size)
    (all : CopyHelperCleanup.AllImmediate frame) : CopyHelperCleanup.AllImmediate (caller frame valid) := by
  let cached := CopyUncachedCall.cachedCaller frame valid
  have cachedAll : CopyHelperCleanup.AllImmediate cached := CopyHelperCleanup.all_immediate_cache frame 18 CopyHelperUnit.layout valid all
  have result := CopyHelperCleanup.all_immediate_set cached 18 ⟨.live (.immediate .uninit),some CopyHelperUnit.layout⟩
    (by simpa [cached,CopyUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout] using valid) cachedAll (by intro memory; simp)
  simpa only [CopyHelperCleanup.AllImmediate,caller,PtrMetadataExecution.writeFrame,cached,CopyUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self] using result
end DuplicatePrefix.CopyRootOutput
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.CopyRootOutput.slot18, ``DuplicatePrefix.CopyRootOutput.metadata,
      ``DuplicatePrefix.CopyRootOutput.other, ``DuplicatePrefix.CopyRootOutput.all_immediate] do
    for dependency in (←collectAxioms declaration) do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "unapproved copy root output {dependency}"
