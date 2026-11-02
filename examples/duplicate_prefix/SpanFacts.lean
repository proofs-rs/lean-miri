import duplicate_prefix.RootCompilerFacts
/-! Exact source declaration spans for the root. Prefix distinctness is
proved using (lo, hi), avoiding expensive comparisons of rendered payloads.
The selected entries are still checked against the complete SourceSpanData. -/
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
namespace DuplicatePrefix.SpanFacts
open Miri Miri.ABI Miri.Input Miri.Interpreter

def spanKey (span : SourceSpanData) := (span.lo, span.hi)

theorem index_of_unique_key (spans : Array SourceSpanData) (target : SourceSpanData) (index : Nat)
    (bound : index < spans.size) (entry : spans[index] = target)
    (unique : (spans.toList.take index).all (fun span => spanKey span != spanKey target) = true) :
    spans.toList.idxOf? target = some index := by
  apply List.idxOf?_eq_some_iff.mpr
  refine ⟨by simpa using bound, by simpa using entry, ?_⟩
  intro j earlier equal
  have member : target ∈ spans.toList.take index := by
    apply List.mem_take_iff_getElem.mpr
    exact ⟨j, by simp only [Array.length_toList]; omega, equal⟩
  have different := List.all_eq_true.mp unique target member
  simp at different

noncomputable def rootInputBody : LoweredBody :=
  PreparedReflection.actual.program.bundle.bodies[RootBody.reflected.body.identity.index]'(by decide +kernel)

noncomputable def rootLocalSpan (localId : Fin 25) : SourceSpanData :=
  (rootInputBody.input.locals[localId.val]'(by
    have size : rootInputBody.input.locals.size = 25 := by rfl
    omega)).sourceInfo.span

theorem root_local0_span_index :
    PreparedReflection.actual.program.bundle.spans.toList.idxOf? (rootLocalSpan ⟨0, by decide⟩) = some 601 := by
  refine index_of_unique_key _ _ _ (by decide +kernel) ?_ ?_
  · with_unfolding_all rfl
  · decide +kernel

theorem root_local1_span_index :
    PreparedReflection.actual.program.bundle.spans.toList.idxOf? (rootLocalSpan ⟨1, by decide⟩) = some 602 := by
  refine index_of_unique_key _ _ _ (by decide +kernel) ?_ ?_
  · with_unfolding_all rfl
  · decide +kernel

theorem root_local2_span_index :
    PreparedReflection.actual.program.bundle.spans.toList.idxOf? (rootLocalSpan ⟨2, by decide⟩) = some 603 := by
  refine index_of_unique_key _ _ _ (by decide +kernel) ?_ ?_
  · with_unfolding_all rfl
  · decide +kernel
open Lean Elab Command in
run_cmd do
  for declaration in #[``index_of_unique_key, ``root_local0_span_index,
      ``root_local1_span_index, ``root_local2_span_index] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"

end DuplicatePrefix.SpanFacts
