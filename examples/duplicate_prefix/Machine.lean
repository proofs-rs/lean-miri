import duplicate_prefix.RootBody
import duplicate_prefix.Prepared
import Miri.Input.EvalConfigurationCore
import Miri.Input.EvalPreparation
import Miri.Interpreter.ExecutionMachine

/-! A deliberately explicit client boundary for the canonical source-built
execution configuration. The compiler products and residual host semantics
are inputs; this file supplies no replacement success callbacks. -/

namespace DuplicatePrefix.Machine

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

/-- Residual hooks for the fixed managed, race-tracking-disabled profile. Core MIR, stack,
memory, retag, and call operations are supplied by canonical `make`. External
sync/native/math/foreign capabilities fail explicitly if reached. -/
def leaves (prepared : EvalPreparation.Prepared) (debugAssertions : Bool) : RootLeaves where
  pointerSource := {
    nativeLibraryPaths := fun _ => #[]
    nativeHost := none }
  sync := fun _ _ => do
    throw (.unsupported "duplicate_prefix profile has no synchronization host")
  storage := fun size _ => some (Array.replicate size.bytesNat 0)
  spans := ⟨prepared.dummySpan, debugAssertions⟩
  foreign := none
  dynSymName := fun _ => "unresolved dynamic symbol"
  checkLlvmSymbolClash := fun _ => do
    throw (.unsupported "duplicate_prefix profile has no LLVM/native symbol resolver")
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

/-- The concrete root-profile builder uses the actual reflected prepared
compiler/image and global-byte catalog with the canonical source builder. -/
def rootConfig (prepared : EvalPreparation.Prepared)
    (bytes : CompilerGlobalBytes.Prepared)
    (options : EvalConfigurationCore.Options) (choice : Unit) (capacity : Nat) :=
  EvalConfigurationCore.make prepared.compiler prepared.image bytes options
    (leaves prepared options.place.debugAssertions) choice capacity

/-- Fixed-input instance: use the compiler, allocation image, and byte catalog
actually produced for this exported example. -/
def actualConfig (options : EvalConfigurationCore.Options)
    (choice : Unit) (capacity : Nat) :=
  rootConfig DuplicatePrefix.PreparedReflection.actual.prepared
    DuplicatePrefix.PreparedReflection.actual.bytes options choice capacity

/-- Actual step boundary for the concrete root profile; caller-supplied state
must still satisfy its own machine/entry invariants. -/
def rootStep [DecidableEq MiriMemoryKind]
    (prepared : EvalPreparation.Prepared) (bytes : CompilerGlobalBytes.Prepared)
    (options : EvalConfigurationCore.Options) (choice : Unit) (capacity : Nat)
    (state : MachineHooks.State MiriMemoryKind RootUser) :
    Except StepError
      (ExecutionMachine.Config MiriMemoryKind RootUser Unit Unit Miri.ABI.ExternAbi Unit ×
        (MachineHooks.State MiriMemoryKind RootUser × Except StepError Bool)) := do
  let config ← rootConfig prepared bytes options choice capacity
  pure (config, ExecutionMachine.step config options.limits choice state)

/-- Same actual machine step boundary, with prepared compiler products fixed
to the reflected duplicate_prefix export. -/
def actualRootStep [DecidableEq MiriMemoryKind]
    (options : EvalConfigurationCore.Options) (choice : Unit) (capacity : Nat)
    (state : MachineHooks.State MiriMemoryKind RootUser) :
    Except StepError
      (ExecutionMachine.Config MiriMemoryKind RootUser Unit Unit Miri.ABI.ExternAbi Unit ×
        (MachineHooks.State MiriMemoryKind RootUser × Except StepError Bool)) := do
  let config ← actualConfig options choice capacity
  pure (config, ExecutionMachine.step config options.limits choice state)

/-- Build the production Core configuration for an explicitly supplied set
of compiler products and genuine residual leaves. This is the same canonical
`EvalConfigurationCore.make` used by source execution, with the finite
callback capacity kept explicit. -/
def canonicalConfig {Os R P H D O Aff B Host C ClockHost : Type}
    (prepared : EvalPreparation.Prepared)
    (bytes : CompilerGlobalBytes.Prepared)
    (options : EvalConfigurationCore.Options)
    (leaves : EvalConfigurationCore.Leaves Os R P H D O Aff B Host C ClockHost)
    (choice : C) (callbackCapacity : Nat) :=
  EvalConfigurationCore.make prepared.compiler prepared.image bytes options leaves choice callbackCapacity

/-- One genuine `ExecutionMachine.step`, after canonical configuration
construction succeeds. This exposes configuration errors separately from
step outcomes and does not identify an arbitrary state as a valid entry. -/
def oneStep {Os R P H D O Aff B Host C ClockHost : Type}
    [DecidableEq MiriMemoryKind]
    (prepared : EvalPreparation.Prepared)
    (bytes : CompilerGlobalBytes.Prepared)
    (options : EvalConfigurationCore.Options)
    (leaves : EvalConfigurationCore.Leaves Os R P H D O Aff B Host C ClockHost)
    (choice : C) (callbackCapacity : Nat)
    (state : MachineHooks.State MiriMemoryKind
      (EvalConfigurationCore.User Os R P H D O Aff B Host)) :
    Except StepError
      (ExecutionMachine.Config MiriMemoryKind
        (EvalConfigurationCore.User Os R P H D O Aff B Host) C O Miri.ABI.ExternAbi ClockHost ×
       (MachineHooks.State MiriMemoryKind
        (EvalConfigurationCore.User Os R P H D O Aff B Host) × Except StepError Bool)) := do
  let config ← canonicalConfig prepared bytes options leaves choice callbackCapacity
  pure (config, ExecutionMachine.step config options.limits choice state)

end DuplicatePrefix.Machine
