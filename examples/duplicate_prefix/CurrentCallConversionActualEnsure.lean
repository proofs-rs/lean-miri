import duplicate_prefix.CurrentCallConversionMaterialize
import duplicate_prefix.CurrentCallOrdinaryInput
import duplicate_prefix.GlobalDataOnlyActualConfig

/-! One actual CURRENT memory/internal-static materialization dispatcher.
The finite converter supplies the internal adjust equation at the real ensure
phase. Static initialization uses the actual imported row; no successful
initializer callback is an input-validity field. -/
namespace DuplicatePrefix.CurrentCallConversionActualEnsure
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open CurrentCallResourceNormalization
open CanonicalConfigFacts CurrentCallOrdinaryInput CurrentCallConversionMaterialize
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

abbrev hooks (options : EvalConfigurationCore.Options) :=
  EvalPointerSource.make PreparedReflection.actual.compiler PreparedReflection.actual.image
    (GlobalDataOnlyActualConfig.extras options)
    (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions).pointerSource ()

/-- The actual original ensure, with all converter changes and the actual
allocation-extra insertion retained. The equation premise is discharged by the
finite converter, not supplied by the ordinary caller. -/
theorem ensure (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (before : RootState) (after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (id : AllocId) (root : BorTag)
    (source : Allocation CtfeProvenance Unit) (converted : Allocation Provenance Unit)
    (current : CurrentPayload before.machine id source)
    (absent : before.machine.memory.live.find? (fun row => row.1 == id) = none)
    (conversion : Allocation.adjustFromTcx source PreparedReflection.actual.compiler.runtime.target.base
      (fun _ _ state => .ok (AllocationCopy.snapshot source) state) (hooks options).rootPointer before.machine =
      .ok converted after)
    (enabled : after.borrowTracker = some tracker) (rootCached : tracker.global.rootTag? id = some root)
    (race : after.dataRace = none)
    (noExtras : (after.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id)) = false) :
    (PreparedContracts.actualConfig options () remaining span).retag.ensureTreeExtra id before =
      .ok () {before with machine := (installed
        (MemoryExtras.putAllocation (GlobalDataOnlyActualConfig.extras options) after id ⟨none, #[]⟩)
        id .global (converted.mapExtra (fun _ => BorrowTree.new root converted.byteSize)))} := by
  let compiler := PreparedReflection.actual.compiler
  let image := PreparedReflection.actual.image
  let extras := GlobalDataOnlyActualConfig.extras options
  let sourceLeaves := (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions).pointerSource
  let constructed := hooks options
  let leaves := GlobalDataOnlyActualBytes.leaves compiler image sourceLeaves constructed.address constructed.rootPointer
  have adjust := CurrentCallConversionMaterialize.adjust_actual compiler image extras sourceLeaves
    constructed.address constructed.rootPointer before.machine after tracker id root source converted
    (by rfl) conversion enabled rootCached race noExtras
  let initializer := fun (memory : MemoryState Provenance BorrowTree MiriMemoryKind)
      (state : PlaceMachine.AccessState MiriMemoryKind Machine.RootUser) (definition : Nat) =>
    let result := image.evaluateStaticInitializer {state with machine := {state.machine with memory}} definition
    (⟨result.state.machine.memory, result.state, result.outcome⟩ :
      GlobalMemoryHookResult Provenance BorrowTree MiriMemoryKind _ (Allocation CtfeProvenance Unit))
  have actual : GlobalAllocationMachine.ensure .global
      (GlobalAllocationMachine.hooks compiler.runtime.target.base extras leaves initializer) id before =
        .ok () {before with machine := (installed (MemoryExtras.putAllocation extras after id ⟨none, #[]⟩)
          id .global (converted.mapExtra (fun _ => BorrowTree.new root converted.byteSize)))} := by
    cases current with
    | memory descriptor =>
      exact ensure_memory compiler.runtime.target.base extras leaves initializer before _ id .global source _ absent descriptor adjust
    | internalStatic definition descriptor row =>
      have initial : initializer before.machine.memory ⟨before.machine, none⟩ definition =
          ⟨before.machine.memory, ⟨before.machine, none⟩, .ok source⟩ := by
        simp only [initializer, image, AllocationImage.Imported.evaluateStaticInitializer, row]
      exact ensure_static compiler.runtime.target.base extras leaves initializer before _ id .global definition source _
        absent descriptor initial adjust
  rw [GlobalDataOnlyActualConfig.actual_ensure]
  exact actual

end DuplicatePrefix.CurrentCallConversionActualEnsure
