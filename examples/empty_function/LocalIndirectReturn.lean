import empty_function.LocalIndirectReturnCopy
import empty_function.ReturnCore
namespace EmptyFunction.LocalIndirectReturn
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
private theorem bound_copy (s : Static) (layout : LocalLayout) (dest : RuntimePlace Provenance)
    (equal : dest.layout = layout)
    (compatible : s.cfg.copy.compatible layout layout = .ok true)
    (padding : s.cfg.copy.hasPadding layout = .ok true) (sized : layout.layout.isSized = true) :
    copyRuntimePlace (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation s.cfg s.limits)).place
      (ExecutionMachine.withValidation s.cfg s.limits).copy () ⟨.immediate .uninit,layout⟩ dest true =
      copyRuntimePlace s.cfg.projection.place s.cfg.copy () ⟨.immediate .uninit,layout⟩ dest true := by
  funext state
  simp [ExecutionMachine.withValidation,ExecutionMachine.projectionHooks,TypedMachineBindings.bindValidation,
    copyRuntimePlace,copyRuntimePlaceNoValidate,equal,compatible,padding,sized,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]

 theorem copy (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2) (positive : 0 < s.options.limits.validation)
    (older : Array LocalUnit.F) (caller : LocalUnit.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser) (id : MIR.LocalId)
    (slot : LocalState Provenance LocalLayout) (memory : MemPlace Provenance) (atSlot : caller.locals[id]? = some slot)
    (live : slot.value = .live (.indirect memory)) (cache : slot.layout = some s.abi.ret.layout) (noMeta : memory.metadata = .none) (aligned : memory.misaligned = none)
    (noClocks : caller.extra.dataRace = none) (noGhost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    (ReturnStep.control s).copyReturn () ⟨.immediate .uninit,s.abi.ret.layout⟩
      (.frameLocal older.size id none s.abi.ret.layout caller.localsIdentity)
      (LocalUnit.current older caller machine) = (LocalUnit.current older caller machine,.ok ()) := by
  have source := BodyPlaceDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes s.options
    (Configuration.leaves s.prepared s.options.place.debugAssertions) (remaining+1) metadata.construction s.cfg
    (by simpa only [Configuration.rootConfig,capacity,Nat.add_assoc] using s.built)
  have compatible : s.cfg.copy.compatible s.abi.ret.layout s.abi.ret.layout = .ok true := by
    rw [source.compatible]
    simp [CompilerCovariance.compatible,CompilerCovariance.relation,CompilerCovariance.relationWithIndex,
      profile.debug,Except.mapError,bind,Except.bind,pure,Except.pure]
  have padding : s.cfg.copy.hasPadding s.abi.ret.layout = .ok true := by
    rw [source.padding]
    simp [CompilerCopy.hasPadding,metadata.unitBackend,pure,Except.pure]
  have eq := bound_copy s s.abi.ret.layout (LocalIndirectReturnCopy.destination older caller id s.abi.ret.layout)
    rfl compatible padding metadata.unitSized
  have safe := LocalIndirectReturnCopy.unit s metadata profile remaining capacity positive older caller machine
    id slot memory atSlot live cache noClocks noMeta aligned noGhost shallow
  change MachineHooks.run (copyRuntimePlace _ _ () _ _ true) (LocalUnit.current older caller machine) = _
  simp only [RuntimeStackPlace.toRuntimePlace]
  change MachineHooks.run (copyRuntimePlace _ _ () _ (LocalIndirectReturnCopy.destination older caller id s.abi.ret.layout) true) _ = _
  rw [eq]
  simp only [MachineHooks.run,Call.run,safe]


end EmptyFunction.LocalIndirectReturn
