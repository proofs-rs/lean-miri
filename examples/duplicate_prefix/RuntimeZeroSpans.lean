import duplicate_prefix.RuntimeZeroEntryFacts
import duplicate_prefix.MetadataSpans

/-! The runtime guard's return-place span is queried from the retained compiler
    body and span table, then fed to the production localSpan hook. -/
namespace DuplicatePrefix.RuntimeZeroSpans
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
open DuplicatePrefix
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

def inputBody : LoweredBody := PreparedReflection.actual.program.bundle.bodies[
  CopyPreconditions.Bodies.languageRuntime.loaded.identity.index]'(by decide +kernel)

def localSpan : SourceSpanData :=
  (inputBody.input.locals[0]'(by decide +kernel)).sourceInfo.span

def spans := PreparedReflection.actual.program.bundle.spans
def spanKeyQuery := (spans.toList.map SpanFacts.spanKey).idxOf? (SpanFacts.spanKey localSpan)
theorem span_key_supported : spanKeyQuery.isSome = true := by decide +kernel
def spanIndex : Nat := spanKeyQuery.get (by simpa using span_key_supported)
theorem span_key_query_eq : spanKeyQuery = some spanIndex := Option.eq_some_of_isSome span_key_supported

theorem span_query_eq : spans.toList.idxOf? localSpan = some spanIndex := by
  have found := List.idxOf?_eq_some_iff.mp span_key_query_eq
  rcases found with ⟨boundKey, _, _⟩
  have bound : spanIndex < spans.size := by
    simpa [Array.length_toList] using boundKey
  have entry : spans[spanIndex] = localSpan := by with_unfolding_all rfl
  exact SpanFacts.index_of_unique_key spans localSpan spanIndex bound entry (by decide +kernel)

theorem body_of_frame (frame : CompilerFrameContext.ActualFrame)
    (body : frame.body = CopyPreconditions.Bodies.languageRuntime.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.languageRuntime.loaded.identity)
    (callee : frame.functionInstance = GuardCompilerFacts.runtimeCall.callee) :
    CompilerFrameContext.bodyOfFrame PreparedReflection.actual.compiler frame = .ok inputBody := by
  unfold CompilerFrameContext.bodyOfFrame
  rw [body, identity, callee]
  with_unfolding_all rfl

theorem runtime_local_span_from_metadata
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = CopyPreconditions.Bodies.languageRuntime.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.languageRuntime.loaded.identity)
    (callee : frame.functionInstance = GuardCompilerFacts.runtimeCall.callee) :
    CompilerFrameContext.localSpan PreparedReflection.actual.compiler
      CopyPreconditions.Bodies.languageRuntime.loaded.body 0 (Storage.withCurrent framesBefore frame machine) =
      .ok ⟨spanIndex⟩ (Storage.withCurrent framesBefore frame machine) := by
  have valid : 0 < inputBody.input.locals.size := by decide +kernel
  let decl := inputBody.input.locals[0]'valid
  have present : inputBody.input.locals[0]? = some decl := by simp [decl, valid]
  have sourceBody := body_of_frame frame body identity callee
  exact MetadataSpans.local_span_from_metadata _ _ _ _ _ 0 inputBody decl localSpan spanIndex
    body.symm sourceBody present rfl span_query_eq

theorem actual_local_span (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = CopyPreconditions.Bodies.languageRuntime.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.languageRuntime.loaded.identity)
    (callee : frame.functionInstance = GuardCompilerFacts.runtimeCall.callee) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).localSpan
      CopyPreconditions.Bodies.languageRuntime.loaded.body 0 (Storage.withCurrent framesBefore frame machine) =
      .ok ⟨spanIndex⟩ (Storage.withCurrent framesBefore frame machine) := by
  change (PreparedContracts.actualConfig options () remaining span).compiler.localSpan _ _ _ = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).compilerLocalSpan]
  exact runtime_local_span_from_metadata framesBefore frame machine body identity callee

end
end DuplicatePrefix.RuntimeZeroSpans

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.RuntimeZeroSpans.body_of_frame,
      ``DuplicatePrefix.RuntimeZeroSpans.runtime_local_span_from_metadata,
      ``DuplicatePrefix.RuntimeZeroSpans.actual_local_span] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved runtime span dependency {dependency}"
