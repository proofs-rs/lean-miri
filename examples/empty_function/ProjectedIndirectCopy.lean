import empty_function.ProjectedIndirectValidation
import empty_function.ProjectedCopy
import empty_function.FactoryProjection
import empty_function.ProjectionWrapping
namespace EmptyFunction.ProjectedIndirectCopy
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem forced (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F) (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout) (memory : MemPlace Provenance) (amount : Size)
    (atSlot : frame.locals[id]? = some slot) (live : slot.value = .live (.indirect memory)) :
    forceAllocation s.cfg.projection.place () ⟨.local frames.size id (some amount) frame.localsIdentity,s.abi.ret.layout⟩
      (LocalUnit.current frames frame machine) =
      .ok ⟨ProjectedIndirectPreflight.shifted memory amount,s.abi.ret.layout⟩ (LocalUnit.current frames frame machine) := by
  let leaves := Configuration.leaves s.prepared s.options.place.debugAssertions
  have built : EvalConfigurationCore.make s.prepared.compiler s.prepared.image s.bytes s.options leaves ()
      ((remaining+1)+1) = .ok s.cfg := by simpa only [Configuration.rootConfig,capacity,Nat.add_assoc] using s.built
  have fields := BodyPlaceDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes s.options
    leaves (remaining+1) metadata.construction s.cfg built
  have debug := (MetadataBinding.fields s metadata (by omega)).debug.trans profile.debug
  have got := LocalIndirectRead.get_operand frame id slot atSlot memory live
  rw [fields.projection]
  rw [ProjectedForce.indirect s.cfg.access s.cfg.allocation s.cfg.compiler () frames frame machine id (some amount)
    s.abi.ret.layout frame.localsIdentity memory got debug]
  have memoryEq := (FactoryProjection.fields s metadata (by omega)).memory
  simp only [ValidityMachine.placeHooks,ValidityMachine.compilerPolicy,PlaceMachine.placeHooks]
  rw [memoryEq]
  simp only [FactoryProjection.action,ProjectionWrapping.source s metadata,
    ProjectedIndirectPreflight.shifted,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]

 theorem control_copy (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2) (positive : 0 < s.options.limits.validation)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F) (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout) (base : LocalLayout)
    (memory : MemPlace Provenance) (amount : Size)
    (atSlot : frame.locals[id]? = some slot) (live : slot.value = .live (.indirect memory))
    (cache : slot.layout = some base) (noClocks : frame.extra.dataRace = none)
    (aligned : memory.misaligned = none)
    (noGhost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (inbounds : EvalProjectionMachine.memoryOffset (ConcreteProtection.source s).pointers
      (BodyValidation.active (LocalUnit.current frames frame machine)) memory amount .inbounds .none =
      .ok (ProjectedIndirectPreflight.shifted memory amount)) :
    (ReturnStep.control s).copyReturn () ⟨.immediate .uninit,s.abi.ret.layout⟩
      (.frameLocal frames.size id (some amount) s.abi.ret.layout frame.localsIdentity)
      (LocalUnit.current frames frame machine) = (LocalUnit.current frames frame machine,.ok ()) := by
  have wrap := ProjectionWrapping.source s metadata (BodyValidation.active (LocalUnit.current frames frame machine)) memory amount
  have validated := ProjectedIndirectValidation.validate_projected s metadata profile remaining capacity positive frames frame machine
    id slot base memory (ProjectedIndirectPreflight.shifted memory amount) amount atSlot live cache noClocks noGhost shallow inbounds wrap
  have forceEq := forced s metadata profile remaining capacity frames frame machine id slot memory amount atSlot live
  exact ProjectedCopy.control_from_force s metadata profile remaining capacity _ _ frames.size id amount frame.localsIdentity
    ⟨ProjectedIndirectPreflight.shifted memory amount,s.abi.ret.layout⟩ rfl rfl aligned forceEq shallow validated
end EmptyFunction.ProjectedIndirectCopy
