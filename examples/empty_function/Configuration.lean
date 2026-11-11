import Miri.Input.EvalConfigurationCore
import Miri.Input.EvalPreparation
import Miri.Interpreter.ExecutionMachine

/-! A deliberately explicit client boundary for the canonical source-built
execution configuration. The compiler products and residual host semantics
are inputs; this file supplies no replacement success callbacks. -/

namespace EmptyFunction.Configuration

open Miri.ABI Miri.Input Miri.Interpreter Miri.Memory

/-- Small explicit host payload for this isolated canonical-core profile.
Time is virtual (`ClockHost = Unit`); event counters and the weak I/O source
set are still stored and updated. No platform or native backend is implied. -/
structure MinimalHost where
  control : TerminatorMachine.Control Unit
  ioSources : Array (Miri.Interpreter.Files.FdId ×
    Miri.Interpreter.BlockingIo.Source)

abbrev RootUser := EvalConfigurationCore.User Unit Unit Unit Unit Unit Unit Unit Unit MinimalHost
abbrev RootLeaves := EvalConfigurationCore.Leaves
  Unit Unit Unit Unit Unit Unit Unit Unit MinimalHost Unit Unit

/-- Residual hooks for the fixed managed, non-GenMC profile. Core MIR, stack,
memory, retag, and call operations are supplied by canonical `make`. External
sync/native/math/foreign capabilities fail explicitly if reached. -/
def leaves (prepared : EvalPreparation.Prepared) (debugAssertions : Bool) : RootLeaves where
  pointerSource := {
    nativeLibraryPaths := fun _ => #[]
    nativeHost := none }
  sync := fun _ _ => do
    throw (.unsupported "empty_function profile has no synchronization host")
  storage := fun size _ => some (Array.replicate size.bytesNat 0)
  spans := ⟨prepared.dummySpan, debugAssertions⟩
  foreign := none
  dynSymName := fun _ => "unresolved dynamic symbol"
  checkLlvmSymbolClash := fun _ => do
    throw (.unsupported "empty_function profile has no LLVM/native symbol resolver")
  math := none
  mathError := .none
  control := {
    get := fun host => host.control
    put := fun control host => {host with control} }
  blockingSources := {
    get := fun host => host.ioSources
    put := fun host sources => {host with ioSources := sources} }

/-- Explicit finite-run options for the isolated x86_64 example. Limits and
retag parameters remain caller inputs; they are not universal resource facts. -/
def exampleOptions (limits : ExecutionMachine.Limits)
    (dynamicFuel compatibilityBudget varArgsBudget callbackCapacity : Nat)
    (validation : ValidityMachine.ValidationMode)
    (retag : CompilerRetagOptions.Options) : EvalConfigurationCore.Options := {
  place := { debugAssertions := false, dynamicFuel, validation }
  limits
  compatibilityBudget
  varArgsBudget
  callbackCapacity
  floatNondeterministic := false
  weakFailureRate := 0
  crossCrateInlineAlways := false
  userRelevantCrates := #[]
  ignoreOptionalOverflowChecks := false
  panicUnwinds := true
  retag }

/-- The fixed proof profile predates optional allocation-backtrace diagnostics.
Preserve every existing caller option while keeping that new diagnostic off.
The proof does not cover the opt-in collector; raw options with that flag set
are interpreted through this explicit legacy-profile projection. -/
abbrev proofOptions (options : EvalConfigurationCore.Options) : EvalConfigurationCore.Options :=
  {options with collectLeakBacktraces := false}

/-- Every diagnostic-off option record embeds unchanged in the proof profile. -/
theorem proofOptions_of_disabled (options : EvalConfigurationCore.Options)
    (disabled : options.collectLeakBacktraces = false) : proofOptions options = options := by
  cases options
  simp_all [proofOptions]

/-- Canonical builder with explicit compiler products and the diagnostic-off
proof profile. Caller metadata may extend the fixed empty_function body; no
whole-document equality is imposed. All pre-existing options remain arbitrary. -/
def rootConfig (prepared : EvalPreparation.Prepared)
    (bytes : CompilerGlobalBytes.Prepared)
    (options : EvalConfigurationCore.Options) (choice : Unit) (capacity : Nat) :=
  EvalConfigurationCore.make prepared.compiler prepared.image bytes (proofOptions options)
    (leaves prepared options.place.debugAssertions) choice capacity


end EmptyFunction.Configuration
