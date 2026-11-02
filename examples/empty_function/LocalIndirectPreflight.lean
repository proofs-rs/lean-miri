import empty_function.LocalIndirectRead
import empty_function.LocalPreflight
namespace EmptyFunction.LocalIndirectPreflight
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
 theorem operand (s : Static) (metadata : Metadata s) (profile : Profile s) (capacity : 0 < s.capacity)
    (p : Packet) (tracker : MachineHooks.BorrowState) (destination : InputDraft.LocalDestination s p tracker)
    (whole : destination.offset = none) (place : MemPlace Provenance)
    (indirect : destination.oldOperand = .indirect place)
    (noClocks : destination.caller.extra.dataRace = none)
    (older : Array LocalUnit.F) (original : p.before.stack.frames = older.push destination.caller)
    (bound : destination.localId < destination.caller.locals.size) :
    (ExecutionMachine.callHooks s.cfg s.limits).placeToOp () p.destination p.before =
      .ok ⟨.indirect place,s.abi.ret.layout⟩
        (LocalUnit.current older (LocalImmediate.cached destination.caller destination.localId destination.slot
          s.abi.ret.layout bound) p.before.machine) := by
  have layout : destination.baseLayout = s.abi.ret.layout := by
    cases destination
    cases whole
    assumption
  have dictionaries := MetadataBinding.fields s metadata capacity
  obtain ⟨remaining,capacityEq⟩ : ∃ n : Nat, s.capacity = n+1 := ⟨s.capacity-1,by omega⟩
  have places := BodyPlaceDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes s.options
    (Configuration.leaves s.prepared s.options.place.debugAssertions) remaining metadata.construction s.cfg
    (by simpa only [Configuration.rootConfig,capacityEq] using s.built)
  have computed : s.cfg.compiler.layout () destination.localId
      (LocalUnit.current older destination.caller p.before.machine) =
      .ok s.abi.ret.layout (LocalUnit.current older destination.caller p.before.machine) := by
    rw [dictionaries.layout]
    unfold CompilerFrameContext.computeLocalLayout
    simp [MachineHooks.currentFrame,LocalUnit.current,Stack.currentFrame?,destination.metadata.normalization,
      get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
    simp_all!
    simp [pure,Pure.pure,EStateM.pure,destination.metadata.lookup,Except.mapError,layout]
    rfl
  have live : destination.slot.value = .live (.indirect place) := by rw [destination.live,indirect]
  have cache : destination.slot.layout = none ∨ destination.slot.layout = some s.abi.ret.layout := by
    simpa only [layout] using destination.cache
  have result := LocalIndirectRead.whole_preflight s.cfg.access s.cfg.allocation s.cfg.compiler () older destination.caller
    p.before.machine destination.localId destination.slot s.abi.ret.layout place bound destination.slotAt live cache
    computed (dictionaries.debug.trans profile.debug)
  have source : (ExecutionMachine.callHooks s.cfg s.limits).placeToOp () p.destination =
      placeToOp s.cfg.projection.place () p.destination.toRuntimePlace := rfl
  rw [source,places.projection,destination.encoding]
  simp only [whole,RuntimeStackPlace.toRuntimePlace,original,Array.size_push,Nat.add_sub_cancel]
  have before : p.before = LocalUnit.current older destination.caller p.before.machine := by
    cases stateEq : p.before with
    | mk stack machine =>
      cases stack with
      | mk frames => simp_all [LocalUnit.current]
  rw [before]
  exact result

end EmptyFunction.LocalIndirectPreflight
