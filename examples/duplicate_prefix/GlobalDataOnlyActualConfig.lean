import duplicate_prefix.CanonicalConfigFacts
import duplicate_prefix.GlobalDataOnlyActualSource

/-! Preserve the lazy-global factory in the actual retag callback identity.
The extras lens is the real shared runtime registry. -/
namespace DuplicatePrefix.GlobalDataOnlyActualConfig
open Miri Miri.Input Miri.ABI Miri.Interpreter Miri.Memory
open CanonicalConfigFacts
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def pointers (compiler : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (leaves : Machine.RootLeaves) (choice : Unit) : RootPointers :=
  (EvalPointerSource.make compiler image
    (EvalCoreMachine.extras leaves.sync ConcurrencyErrors.storeBuffer) leaves.pointerSource
    choice).pointers

private theorem make_ensure (p : CompilerProviders.Prepared)
    (image : AllocationImage.Imported) (bytes : CompilerGlobalBytes.Prepared)
    (options : EvalConfigurationCore.Options) (leaves : Machine.RootLeaves)
    (choice : Unit) (remaining : Nat) (contract : PreparedContracts.CompilerConstruction p) :
    ∃ config, EvalConfigurationCore.make p image bytes options leaves choice (remaining + 1) = .ok config ∧
      config.retag.ensureTreeExtra = (pointers p image leaves choice).ensureTreeExtra := by
  unfold EvalConfigurationCore.make
  unfold_factory_helpers
  rw [EvalConfigurationCore.makeWithForeignContext]
  simp (config := {zeta := false}) only [contract.maximum_eq]
  unfold_factory_helpers
  simp (config := {zeta := false}) only [EvalMathMachine.hooks,
    CompilerCallConstruction.helpers, contract.i32_eq, contract.bool_eq,
    contract.u8_eq, contract.unit_eq, contract.rootSpan_eq,
    Except.mapError, Except.map, bind, Except.bind, pure, Except.pure]
  refine ⟨_, rfl, ?_⟩
  with_unfolding_all rfl

theorem actual_ensure (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    (PreparedContracts.actualConfig options choice remaining span).retag.ensureTreeExtra =
      (pointers PreparedReflection.actual.compiler PreparedReflection.actual.image
        (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions) choice).ensureTreeExtra := by
  obtain ⟨config,construction,field⟩ := make_ensure PreparedReflection.actual.compiler
    PreparedReflection.actual.image PreparedReflection.actual.bytes options
    (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions)
    choice remaining (PreparedContracts.actualConstruction span)
  have eq := PreparedContracts.actualConfig_eq options choice remaining span
  change EvalConfigurationCore.make PreparedReflection.actual.compiler PreparedReflection.actual.image
    PreparedReflection.actual.bytes options
    (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions)
    choice (remaining + 1) = .ok _ at eq
  rw [construction] at eq
  have same : config = PreparedContracts.actualConfig options choice remaining span := Except.ok.inj eq
  exact same ▸ field
def extras (options : EvalConfigurationCore.Options) : RootExtras :=
  EvalCoreMachine.extras
    (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions).sync
    ConcurrencyErrors.storeBuffer

theorem ensure_success (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : RootState) (tracker : MachineHooks.BorrowState)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit)
    (supported : GlobalSupportedImage.Supported source PreparedReflection.actual.compiler.runtime.target
      before.machine.memory tracker.global.rootPointerTags before.machine.user.addresses.baseAddr)
    (enabled : before.machine.borrowTracker = some tracker)
    (rootCached : tracker.global.rootTag? id = some root)
    (race : before.machine.dataRace = none)
    (noExtras : (before.machine.user.payload.payload.user.runtime.extras.allocations.any
      (fun row => row.1 == id)) = false)
    (absent : (before.machine.memory.live.find? (fun old => old.1 == id)) = none)
    (descriptor : before.machine.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩) :
    ∃ converted : Allocation Provenance Unit,
      GlobalAllocationAttributes.Attributes source converted ∧
      (PreparedContracts.actualConfig options choice remaining span).retag.ensureTreeExtra id before =
        .ok () {before with machine := (GlobalDataOnlyMaterialize.cached (extras options) before.machine id .global
          (converted.mapExtra (fun _ => Miri.TreeBorrows.BorrowTree.new root source.byteSize)))} := by
  rw [actual_ensure]
  exact GlobalDataOnlyActualSource.ensure PreparedReflection.actual.compiler PreparedReflection.actual.image
    (extras options) (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions).pointerSource
    choice before tracker id root source (by rfl) supported enabled rootCached race noExtras absent descriptor

end DuplicatePrefix.GlobalDataOnlyActualConfig

open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.GlobalDataOnlyActualConfig.actual_ensure,
      ``DuplicatePrefix.GlobalDataOnlyActualConfig.ensure_success] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved actual global factory dependency {dependency}"
