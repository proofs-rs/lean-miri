import duplicate_prefix.CopyEntryLocals
namespace DuplicatePrefix.CopyEntrySpans
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
noncomputable def spanAt (index : Fin 4) : Nat := #[619,620,621,622][index.val]
 theorem cases_four (index : Fin 4) : index=0 ∨ index=1 ∨ index=2 ∨ index=3 := by
  by_cases h0 : index=0
  · exact .inl h0
  by_cases h1 : index=1
  · exact .inr (.inl h1)
  by_cases h2 : index=2
  · exact .inr (.inr (.inl h2))
  have n0 : index.val ≠ 0 := fun eq => h0 (Fin.ext eq)
  have n1 : index.val ≠ 1 := fun eq => h1 (Fin.ext eq)
  have n2 : index.val ≠ 2 := fun eq => h2 (Fin.ext eq)
  exact .inr (.inr (.inr (Fin.ext (by have :=index.isLt;omega))))
noncomputable def inputIndex (index : Fin 4) : Fin 17 := ⟨index.val,by have := index.isLt;omega⟩
 theorem span_index (index : Fin 4) :
    PreparedReflection.actual.program.bundle.spans.toList.idxOf? (CopyEntryLocals.localSpan (inputIndex index)) = some (spanAt index) := by
  rcases cases_four index with rfl | rfl | rfl | rfl
  all_goals
    refine SpanFacts.index_of_unique_key _ _ _ (by decide +kernel) ?_ ?_
    · with_unfolding_all rfl
    · decide +kernel
 theorem local_span
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee) (index : Fin 4) :
    CompilerFrameContext.localSpan PreparedReflection.actual.compiler HelperCompilerFacts.copyBody.body index.val
      (Storage.withCurrent frames frame machine) = .ok ⟨spanAt index⟩ (Storage.withCurrent frames frame machine) := by
  have valid : index.val < CopyEntryLocals.inputBody.input.locals.size := by
    have size : CopyEntryLocals.inputBody.input.locals.size = 17 := by rfl
    rw [size]
    have := index.isLt
    omega
  let decl := CopyEntryLocals.inputBody.input.locals[index.val]'valid
  have present : CopyEntryLocals.inputBody.input.locals[index.val]? = some decl := by simp [decl,valid]
  exact MetadataSpans.local_span_from_metadata _ _ _ _ _ _ CopyEntryLocals.inputBody decl _ (spanAt index) body.symm
    (CopyEntryLocals.body_of_frame frame body identity callee) present rfl (span_index index)
end DuplicatePrefix.CopyEntrySpans
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.CopyEntrySpans.local_span) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved copy source local span {dependency}"
