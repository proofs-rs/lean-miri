import duplicate_prefix.GlobalDataOnlyActualConfig
import duplicate_prefix.StaticGlobalActualSource

namespace DuplicatePrefix.StaticGlobalActualConfig
open Miri Miri.Input Miri.ABI Miri.Interpreter Miri.Memory
open CanonicalConfigFacts
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
abbrev extras := GlobalDataOnlyActualConfig.extras

/-- Real fixed-config STATIC materialization from the exported initializer row
and raw supported-image/metadata resources, rather than an assumed callback. -/
theorem ensure_success (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : RootState) (tracker : MachineHooks.BorrowState)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit) (definition : Nat)
    (initializer : PreparedReflection.actual.image.initializers.find? (·.1 == definition) = some (definition,source))
    (supported : GlobalSupportedImage.Supported source PreparedReflection.actual.compiler.runtime.target
      before.machine.memory tracker.global.rootPointerTags before.machine.user.addresses.baseAddr)
    (enabled : before.machine.borrowTracker = some tracker)
    (rootCached : tracker.global.rootTag? id = some root)
    (race : before.machine.dataRace = none)
    (noExtras : (before.machine.user.payload.payload.user.runtime.extras.allocations.any
      (fun row => row.1 == id)) = false)
    (absent : (before.machine.memory.live.find? (fun old => old.1 == id)) = none)
    (descriptor : before.machine.memory.findGlobal? id = some
      ⟨id,.static,source.byteSize,source.align,source.mutability,some (.static definition true false false)⟩) :
    ∃ converted : Allocation Provenance Unit,
      GlobalAllocationAttributes.Attributes source converted ∧
      (PreparedContracts.actualConfig options choice remaining span).retag.ensureTreeExtra id before =
        .ok () {before with machine := (GlobalDataOnlyMaterialize.cached (extras options) before.machine id .global
          (converted.mapExtra (fun _ => Miri.TreeBorrows.BorrowTree.new root source.byteSize)))} := by
  rw [GlobalDataOnlyActualConfig.actual_ensure]
  exact StaticGlobalActualSource.ensure PreparedReflection.actual.compiler PreparedReflection.actual.image
    (extras options) (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions).pointerSource
    choice before tracker id root definition source initializer (by rfl) supported enabled rootCached race noExtras absent descriptor

end DuplicatePrefix.StaticGlobalActualConfig
