import duplicate_prefix.ActualLocalCopy
namespace DuplicatePrefix.LenCallResultFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable def resultFrame (caller : CompilerFrameContext.ActualFrame) (valid : 11 < caller.locals.size) (len : UInt64) :=
  {ActualLocalCopy.written caller 11 RootCompilerFacts.usizeLayout valid (.scalar (.fromScalarInt (.ofUInt64 len)))
    with location := .mir ⟨3,0⟩}

theorem size (caller : CompilerFrameContext.ActualFrame) (valid : 11 < caller.locals.size) (len : UInt64) :
    (resultFrame caller valid len).locals.size = caller.locals.size := by simp [resultFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout]

theorem value (caller : CompilerFrameContext.ActualFrame) (valid : 11 < caller.locals.size) (len : UInt64) :
    (resultFrame caller valid len).locals[11]? =
      some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩ := by
  simp [resultFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout]

theorem other (caller : CompilerFrameContext.ActualFrame) (valid : 11 < caller.locals.size) (len : UInt64)
    (index : Nat) (different : index ≠ 11) :
    (resultFrame caller valid len).locals[index]? = caller.locals[index]? := by
  simp [resultFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem?_set,different,Ne.symm different]

theorem attributes (caller : CompilerFrameContext.ActualFrame) (valid : 11 < caller.locals.size) (len : UInt64) :
    let result := resultFrame caller valid len
    result.body = caller.body ∧ result.bodyIdentity = caller.bodyIdentity ∧
    result.functionInstance = caller.functionInstance ∧ result.extra = caller.extra ∧
    result.localsIdentity = caller.localsIdentity ∧ result.returnPlace = caller.returnPlace ∧
    result.returnContinuation = caller.returnContinuation ∧ result.trackCallerArg = caller.trackCallerArg ∧
    result.vaList = caller.vaList ∧ result.location = .mir ⟨3,0⟩ := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem all_immediate (caller : CompilerFrameContext.ActualFrame) (valid : 11 < caller.locals.size) (len : UInt64)
    (source : ∀ slot ∈ caller.locals, ∀ memory, slot.value ≠ .live (.indirect memory)) :
    ∀ slot ∈ (resultFrame caller valid len).locals, ∀ memory, slot.value ≠ .live (.indirect memory) := by
  intro slot member memory
  obtain ⟨index,bound,same⟩ := Array.mem_iff_getElem.mp member
  subst slot
  by_cases selected : index = 11
  · subst index
    simp [resultFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set_self]
  · have original : index < caller.locals.size := by simpa only [size] using bound
    have known := source caller.locals[index] (Array.getElem_mem original) memory
    simpa [resultFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,selected,Ne.symm selected] using known
end DuplicatePrefix.LenCallResultFrame
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.LenCallResultFrame.size, ``DuplicatePrefix.LenCallResultFrame.value,
      ``DuplicatePrefix.LenCallResultFrame.other, ``DuplicatePrefix.LenCallResultFrame.attributes,
      ``DuplicatePrefix.LenCallResultFrame.all_immediate] do
    for dependency in (←collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved len caller frame property {dependency}"
