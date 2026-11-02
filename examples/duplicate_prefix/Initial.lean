import duplicate_prefix.Machine
import duplicate_prefix.FileInitFacts
import duplicate_prefix.FileOwnershipFacts
import Miri.Input.InitialMachine
import Miri.Interpreter.ExecutionStateTransport
import Lean

/-! Real canonical EvalWorld initialization for the fixed example profile.
The imported memory and strict choice tape remain explicit inputs; no initial
memory omission or choice-generation fallback is hidden here. -/

namespace DuplicatePrefix.Initial

open Lean Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
open Miri.Memory.AllocAddresses
open Lean Elab Tactic

elab "simp_valid_rate" : tactic => do
  let env ← getEnv
  let found := env.constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith ".ReusePool.validRate" then some name else none
  let [name] := found | throwError "unique ReusePool.validRate helper"
  let id := mkIdent name
  evalTactic (← `(tactic| simp [$id:ident]))

def geometry : InitialMachine.Geometry := ⟨4096, 131072, 65536⟩

theorem geometry_matches_x86_64 :
    InitialMachine.geometry 64 "x86_64" false none = .ok geometry := by
  rfl

/-- Explicit managed strict-provenance configuration with Tree Borrows
enabled. Scheduling is fixed for this finite example setup; strict random
choices remain supplied by the caller. -/
def configuration (dummySpan : Miri.MIR.SpanRef)
    (validation : ValidityMachine.ValidationMode) :
    InitialMachine.Configuration Unit Unit := {
  geometry
  dummySpan
  provenance := .strict
  addressMode := .managed
  addressStop := 18446744073709551615
  addressReuse := { addressReuseRate := 0.0, addressReuseCrossThreadRate := 0.0 }
  fixedScheduling := true
  trackOutdatedLoads := false
  weakMemory := false
  backend := .none
  trackedTags := some #[]
  validation
  alignment := .Int
  affinity := none
  muteOutput := true
  hostUsizeBits := 64 }

def actualConfiguration (validation : ValidityMachine.ValidationMode) :=
  configuration DuplicatePrefix.PreparedReflection.actual.prepared.dummySpan validation

def fixedHost : Machine.MinimalHost := {
  control := {
    basicBlockCount := 0
    sinceGc := 0
    gcInterval := 0
    monotonic := .virtual 0
    preemptionRateBits := 0
    checkedArithmetic := false }
  ioSources := #[]
 }

def strictEmptyTape : ExecutionChoices.Tape := { inputs := #[], policy := .strict }

/-- Preserve the actual initialisation memory, actual prepared type world,
strict arbitrary choice tape, and caller host while crossing the exact outer
EvalWorld to inner EvalCore state lens. -/
def createState (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (choices : ExecutionChoices.Tape) (host : Machine.MinimalHost)
    (validation : ValidityMachine.ValidationMode) :
    Except StepError (MachineHooks.State MiriMemoryKind Machine.RootUser) := do
  let outer ← InitialMachine.create (actualConfiguration validation) memory
    DuplicatePrefix.PreparedReflection.actual.prepared.types choices host
  pure (ExecutionStateTransport.inward outer)

theorem configuration_is_strict_managed
    (validation : ValidityMachine.ValidationMode) :
    (actualConfiguration validation).provenance = .strict ∧
    (actualConfiguration validation).addressMode = .managed ∧
    (actualConfiguration validation).backend = .none ∧
    (actualConfiguration validation).trackedTags = some #[] := by
  simp [actualConfiguration, configuration]

theorem actual_addresses_exist
    (zeroRateValid : ¬ (Float.le 0.0 0.0 = true → Float.le 0.0 1.0 = false)) :
    ∃ addresses : GlobalAddressState,
      GlobalAddressState.new .strict .managed 131072 18446744073709551615
        { addressReuseRate := 0.0, addressReuseCrossThreadRate := 0.0 } = .ok addresses := by
  have poolOk : ReusePool.new
      { addressReuseRate := 0.0, addressReuseCrossThreadRate := 0.0 } =
        .ok ⟨0.0, 0.0, #[]⟩ := by
    simp [ReusePool.new]
    simp_valid_rate
    simp [zeroRateValid]
    simp [pure, Except.pure]
  refine ⟨⟨#[], #[], #[], .strict, .managed,
    some ⟨AddressGenerator.new 131072 18446744073709551615, ⟨0.0, 0.0, #[]⟩⟩, #[]⟩, ?_⟩
  unfold GlobalAddressState.new
  rw [poolOk]
  rfl

theorem actual_outer_state_exists
    (zeroRateValid : ¬ (Float.le 0.0 0.0 = true → Float.le 0.0 1.0 = false)) :
    ∃ state : EvalWorld.State Unit Unit Unit Unit Unit Unit Unit Unit Machine.MinimalHost,
      InitialMachine.create (actualConfiguration .Shallow)
        DuplicatePrefix.PreparedReflection.actual.initialMemory
        DuplicatePrefix.PreparedReflection.actual.prepared.types strictEmptyTape fixedHost =
          .ok state := by
  obtain ⟨addresses, haddresses⟩ := actual_addresses_exist zeroRateValid
  unfold InitialMachine.create
  simp only [actualConfiguration, configuration, geometry]
  rw [haddresses]
  rw [DuplicatePrefix.FileInitFacts.file_table_exact]
  simp only [Bind.bind, Except.bind]
  erw [DuplicatePrefix.FileOwnershipFacts.initial_ownership_loop
    (Handle := Unit) (Directory := Unit) (Other := Unit) true]
  simp [DuplicatePrefix.FileOwnershipFacts.initialOwnership, Bind.bind,
    Except.bind, Except.mapError, pure, Except.pure]

theorem actual_initial_state_exists
    (zeroRateValid : ¬ (Float.le 0.0 0.0 = true → Float.le 0.0 1.0 = false)) :
    ∃ state : MachineHooks.State MiriMemoryKind Machine.RootUser,
      createState DuplicatePrefix.PreparedReflection.actual.initialMemory
        strictEmptyTape fixedHost .Shallow = .ok state := by
  obtain ⟨outer, houter⟩ := actual_outer_state_exists zeroRateValid
  refine ⟨ExecutionStateTransport.inward outer, ?_⟩
  unfold createState
  rw [houter]
  rfl

/- The pinned ABI query data is preserved in `actual.prepared`. The existing
`CompilerInstanceAbi.Prepared` API intentionally hides its indexed lookup
implementation, and kernel reduction cannot expose this query from the
reflected value. Avoid turning that metadata lookup into an unchecked
runtime-call claim here. -/

end DuplicatePrefix.Initial
