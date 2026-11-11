import empty_function.LocalPreflight
import empty_function.ProjectedMaterialize
import empty_function.FactoryProjectionExact
namespace EmptyFunction.ProjectedImmediatePreflight
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

/-- Pure unit-offset extraction from any enclosing immediate. No scalar
or reference validity is inferred; the projected unit remains uninitialized. -/
theorem offset_value (target : RuntimeTargetDataLayout) (source unit : LocalLayout) (offset : Size) (value : Immediate Provenance)
    (bound : offset.bytes.toNat ≤ source.layout.size.bytes.toNat)
    (unitSize : unit.layout.size = Size.ZERO) (unitSized : unit.layout.isSized = true)
    (backend : unit.layout.backendRepr = .Memory (sized := true)) :
    projectionImmediateOffset (EvalProjectionMachine.assertAbi target) value
      source offset unit false = .ok .uninit := by
  have sizeAdd : offset.add unit.layout.size = .ok offset := by
    simp [unitSize,Size.add,Size.ZERO,Size.ofBytes,UInt64.add_zero]
  have range : ¬source.layout.size.bytes < offset.bytes := UInt64.not_lt.mpr (UInt64.le_iff_toNat_le.mpr bound)
  cases value <;> simp [projectionImmediateOffset,sizeAdd,range,EvalProjectionMachine.assertAbi,backend,
    LayoutData.isZst,unitSize,Size.ZERO,Size.add,Size.ofBytes,UInt64.add_zero,
    BackendRepr.isSized,BackendRepr.isUnsized,Except.mapError,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]

/-- Internal read/cache/offset composition. The pure context equation is later
bound to the actual canonical compiler projection dictionary. -/
theorem operand {K U C : Type} [DecidableEq K]
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C) (choice : C)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout) (base unit : LocalLayout) (offset : Size) (value : Immediate Provenance)
    (bound : id < frame.locals.size) (atSlot : frame.locals[id]? = some slot)
    (live : slot.value = .live (.immediate value))
    (cache : slot.layout = none ∨ slot.layout = some base) (sized : base.layout.isSized = true)
    (computed : compiler.layout choice id (LocalUnit.current frames frame machine) =
      .ok base (LocalUnit.current frames frame machine))
    (debugOff : compiler.debugAssertions = false) (noClocks : frame.extra.dataRace = none)
    (context : ProjectionCx Provenance)
    (projection : compiler.projection choice (LocalUnit.current frames (LocalImmediate.cached frame id slot base bound) machine) =
      .ok context (LocalUnit.current frames (LocalImmediate.cached frame id slot base bound) machine))
    (unitSized : unit.layout.isSized = true)
    (extracted : context.immediateOffset value base offset unit = .ok .uninit) :
    placeToOp (ValidityMachine.placeHooks access allocation compiler) choice
      ⟨.local frames.size id (some offset) frame.localsIdentity,unit⟩ (LocalUnit.current frames frame machine) =
      .ok ⟨.immediate .uninit,unit⟩ (LocalUnit.current frames (LocalImmediate.cached frame id slot base bound) machine) := by
  have lay := LocalImmediate.layout_cached (ValidityMachine.compilerPolicy compiler) choice frames frame machine id slot base bound atSlot cache computed
  have got := LocalImmediate.get_local (LocalImmediate.cached frame id slot base bound) id {slot with layout := some base}
    (LocalImmediate.cached_at frame id slot base bound)
  have operand : (LocalImmediate.cached frame id slot base bound).getLocalOperand id = .ok (.immediate value) := by
    simp [Frame.getLocalOperand,got,LocalState.access,live,Except.mapError,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
  have noClockCached : (LocalImmediate.cached frame id slot base bound).extra.dataRace = none := noClocks
  have localRead : PlaceMachine.localToOp (ValidityMachine.compilerPolicy compiler) choice id
      (LocalUnit.current frames frame machine) =
      .ok ⟨.immediate value,base⟩ (LocalUnit.current frames (LocalImmediate.cached frame id slot base bound) machine) := by
    unfold PlaceMachine.localToOp PlaceMachine.localToOpCore
    simp only [bind,Bind.bind,EStateM.bind]
    rw [lay]
    cases ghost : machine.user.payload.ghost <;> with_unfolding_all
      simp [MachineHooks.currentFrame,LocalUnit.current,Stack.currentFrame?,operand,sized,
        ValidityMachine.compilerPolicy,ValidityMachine.validationInProgress,ghost,MachineHooks.afterLocalRead,
        noClockCached,get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,
        EStateM.pure,Except.pure,Except.bind,Except.mapError]
  unfold placeToOp placeToOpCore
  simp only [ValidityMachine.placeHooks,ValidityMachine.compilerPolicy,PlaceMachine.placeHooks,
    Stack.frameIndex,LocalUnit.current,debugOff,get,getThe,MonadStateOf.get,EStateM.get,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Except.pure,Except.bind,
    Array.isEmpty_push,Array.size_push,Array.back?_push,Nat.add_sub_cancel,
    beq_self_eq_true,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
  simp only [LocalUnit.current,ValidityMachine.compilerPolicy,debugOff] at localRead projection
  rw [localRead]
  simp only [bind,Bind.bind,EStateM.bind]
  rw [projection]
  with_unfolding_all simp [OpTy.offset,OpTy.offsetWithMeta,unitSized,MemPlaceMeta.hasMeta,extracted,
    pure,Pure.pure,EStateM.pure,bind,Bind.bind,EStateM.bind,Except.pure,Except.bind]
  rfl

theorem canonical (s : Static) (metadata : Metadata s) (profile : Profile s) (capacity : 0 < s.capacity)
    (p : Packet) (tracker : MachineHooks.BorrowState) (destination : InputDraft.LocalDestination s p tracker)
    (offset : Size) (projected : destination.offset = some offset) (value : Immediate Provenance)
    (immediate : destination.oldOperand = .immediate value)
    (noClocks : destination.caller.extra.dataRace = none)
    (older : Array LocalUnit.F) (original : p.before.stack.frames = older.push destination.caller)
    (bound : destination.localId < destination.caller.locals.size) :
    (ExecutionMachine.callHooks s.cfg s.limits).placeToOp () p.destination p.before =
      .ok ⟨.immediate .uninit,s.abi.ret.layout⟩
        (LocalUnit.current older (LocalImmediate.cached destination.caller destination.localId destination.slot
          destination.baseLayout bound) p.before.machine) := by
  have dictionaries := MetadataBinding.fields s metadata capacity
  obtain ⟨remaining,capacityEq⟩ : ∃ n : Nat, s.capacity = n+1 := ⟨s.capacity-1,by omega⟩
  have built : EvalConfigurationCore.make s.prepared.compiler s.prepared.image s.bytes (EmptyFunction.Configuration.proofOptions s.options)
      (Configuration.leaves s.prepared s.options.place.debugAssertions) () (remaining+1) = .ok s.cfg := by
    simpa only [Configuration.rootConfig,capacityEq] using s.built
  have places := BodyPlaceDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes (EmptyFunction.Configuration.proofOptions s.options)
    (Configuration.leaves s.prepared s.options.place.debugAssertions) remaining metadata.construction s.cfg built
  have computed : s.cfg.compiler.layout () destination.localId
      (LocalUnit.current older destination.caller p.before.machine) =
      .ok destination.baseLayout (LocalUnit.current older destination.caller p.before.machine) := by
    rw [dictionaries.layout]
    unfold CompilerFrameContext.computeLocalLayout
    simp [MachineHooks.currentFrame,LocalUnit.current,Stack.currentFrame?,destination.metadata.normalization,
      get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
    simp_all!
    simp [pure,Pure.pure,EStateM.pure,destination.metadata.lookup,Except.mapError]
    rfl
  let cached := LocalUnit.current older (LocalImmediate.cached destination.caller destination.localId
    destination.slot destination.baseLayout bound) p.before.machine
  have contextEq := FactoryProjectionExact.projection s.prepared.compiler s.prepared.image s.bytes (EmptyFunction.Configuration.proofOptions s.options)
    (Configuration.leaves s.prepared s.options.place.debugAssertions) remaining metadata.construction s.cfg built cached
  have projectedBound : offset.bytes.toNat ≤ destination.baseLayout.layout.size.bytes.toNat := by
    cases destination
    cases projected
    assumption
  have extracted := offset_value s.prepared.compiler.lifecycle.calls.symbols.facts.context.runtime.target
    destination.baseLayout s.abi.ret.layout offset value projectedBound metadata.unitSize metadata.unitSized metadata.unitBackend
  have result := operand s.cfg.access s.cfg.allocation s.cfg.compiler () older destination.caller p.before.machine
    destination.localId destination.slot destination.baseLayout s.abi.ret.layout offset value bound destination.slotAt
    (by rw [destination.live,immediate]) destination.cache destination.baseSized computed
    (dictionaries.debug.trans profile.debug) noClocks _ contextEq metadata.unitSized
    (by simpa only [EvalProjectionMachine.context,profile.debug] using extracted)
  have source : (ExecutionMachine.callHooks s.cfg s.limits).placeToOp () p.destination =
      placeToOp s.cfg.projection.place () p.destination.toRuntimePlace := rfl
  rw [source,places.projection,destination.encoding]
  simp only [projected,RuntimeStackPlace.toRuntimePlace,original,Array.size_push,Nat.add_sub_cancel]
  have before : p.before = LocalUnit.current older destination.caller p.before.machine := by
    cases stateEq : p.before with
    | mk stack machine =>
      cases stack with
      | mk frames => simp_all [LocalUnit.current]
  rw [before]
  exact result
end EmptyFunction.ProjectedImmediatePreflight
