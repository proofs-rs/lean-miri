import Miri.Interpreter.PointerPlaceMachine
import Miri.Interpreter.ValidityMachine

/- Source-level kernel regressions for the constructor used by the proposed
   pollfd path: the caller-supplied target array element layout is authoritative,
   the raw pointer carries no dynamic metadata, and the helper's sized guard is
   retained. These propositions are checked by Lean's kernel, not native_decide. -/
namespace PollPointerPlaceAudit
open Miri.ABI Miri.Memory Miri.Interpreter

variable {K U : Type}

/-- The fromPointer constructor's successful path records the target layout,
    not any declared pointer pointee layout, and records no metadata. -/
theorem fromPointer_targetLayout_and_metadataNone
    (access : ValidityMachine.Access K U)
    (ptr : Pointer (Option Provenance))
    (targetLayout : LocalLayout)
    (state : ValidityMachine.State K U) :
    PointerPlaceMachine.fromPointer access ptr targetLayout false = (do
      unless targetLayout.layout.isSized do
        throw (.invalidProgram "ptr_to_mplace requires sized layout")
      PointerPlaceMachine.withMetadata access ptr .none targetLayout false) := by
  rfl

/-- The unaligned construction path does not request target alignment
    calculation; poll's actual call must use `false` to retain that check. -/
theorem fromPointer_unaligned_hasNoCachedMisalignment
    (access : ValidityMachine.Access K U)
    (ptr : Pointer (Option Provenance))
    (targetLayout : LocalLayout)
    (state : ValidityMachine.State K U) :
    PointerPlaceMachine.withMetadata access ptr .none targetLayout true = (do
      pure ⟨⟨ptr, .none, none⟩, targetLayout⟩) := by
  simp [PointerPlaceMachine.withMetadata]

/-- For the aligned path, the precise alignment request is derived from the
    supplied target layout's ABI alignment. This guards against accidentally
    constructing from the operand's declared pointee layout. -/
theorem withMetadata_checksTargetAbiAlignment
    (access : ValidityMachine.Access K U)
    (ptr : Pointer (Option Provenance))
    (targetLayout : LocalLayout) :
    PointerPlaceMachine.withMetadata access ptr .none targetLayout false = (do
      let mismatch ← PointerPlaceMachine.misalignment access ptr targetLayout.layout.align.abi
      pure ⟨⟨ptr, .none, mismatch⟩, targetLayout⟩) := by
  rfl

/-- The source ptr_to_mplace sized-layout guard is unchanged and precedes the
    metadata-free place constructor. -/
theorem fromPointer_retainsSizedGuard
    (access : ValidityMachine.Access K U)
    (ptr : Pointer (Option Provenance))
    (targetLayout : LocalLayout) :
    PointerPlaceMachine.fromPointer access ptr targetLayout false = (do
      unless targetLayout.layout.isSized do
        throw (.invalidProgram "ptr_to_mplace requires sized layout")
      PointerPlaceMachine.withMetadata access ptr .none targetLayout false) := by
  rfl

end PollPointerPlaceAudit
