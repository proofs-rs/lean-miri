import empty_function.IndirectProjection
import empty_function.ProjectionZero
import empty_function.ProjectionSnapshot
import empty_function.FactoryProjection
import empty_function.LocalCachedPush
import empty_function.LocalIndirectRead
namespace EmptyFunction.ProjectedIndirectPreflight
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.InputDraft
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def shifted (place : MemPlace Provenance) (amount : Size) : MemPlace Provenance :=
  {place with ptr := {place.ptr with offset := Size.ofBytes (place.ptr.offset.bytes+amount.bytes)},metadata := .none}

theorem source (s : Static) (metadata : Metadata s) (p : Packet) (tracker : MachineHooks.BorrowState)
    (destination : LocalDestination s p tracker) (amount : Size) (offset : destination.offset = some amount)
    (place : MemPlace Provenance) (indirect : destination.oldOperand = .indirect place) :
    EvalProjectionMachine.memoryOffset (ConcreteProtection.source s).pointers p.before place amount .inbounds .none =
      .ok (shifted place amount) := by
  have within : amount.bytes.toNat ≤ destination.baseLayout.layout.size.bytes.toNat := by
    cases destination
    subst_vars
    assumption
  by_cases zero : amount.bytes = 0
  · have same : amount = Size.ZERO := by cases amount;cases zero;rfl
    subst amount
    simpa only [shifted,Size.ZERO,Size.ofBytes,UInt64.add_zero] using ProjectionZero.source s metadata p.before place
  · have parentPositive : destination.baseLayout.layout.size.bytes ≠ 0 := by
      intro nil
      have positive : 0 < amount.bytes.toNat := by
        have ne : amount.bytes.toNat ≠ 0 := by intro n;apply zero;exact UInt64.toNat_inj.mp n
        omega
      rw [nil] at within
      simp only [UInt64.toNat_zero] at within
      omega
    obtain ⟨foot⟩ := destination.oldFootprint (by rw [offset];rfl) parentPositive place indirect
    have tables : place.ptr.provenance = some .wildcard → AddressTables p.before := by
      intro wild
      cases destination.oldPointer place indirect with
      | integer enc => rw [enc] at wild;contradiction
      | concrete id tag base tables enc cached backing parent latent =>
        rw [enc] at wild
        cases Option.some.inj wild
      | wildcard enc mode tables selected => exact tables
    exact IndirectProjection.positive s metadata p.before place destination.baseLayout.layout.size amount
      foot tables zero within destination.baseSigned

theorem local_read {K U C : Type} (compiler : ValidityMachine.Compiler K U C) (choice : C)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F) (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout) (layout : LocalLayout)
    (place : MemPlace Provenance) (bound : id < frame.locals.size) (atSlot : frame.locals[id]? = some slot)
    (live : slot.value = .live (.indirect place)) (cache : slot.layout = none ∨ slot.layout = some layout)
    (computed : compiler.layout choice id (LocalUnit.current frames frame machine) = .ok layout (LocalUnit.current frames frame machine)) :
    PlaceMachine.localToOp (ValidityMachine.compilerPolicy compiler) choice id (LocalUnit.current frames frame machine) =
      .ok ⟨.indirect place,layout⟩ (LocalUnit.current frames (LocalImmediate.cached frame id slot layout bound) machine) := by
  have lay := LocalImmediate.layout_cached (ValidityMachine.compilerPolicy compiler) choice frames frame machine id slot layout bound atSlot cache computed
  have operand := LocalIndirectRead.get_operand (LocalImmediate.cached frame id slot layout bound) id
    {slot with layout := some layout} (LocalImmediate.cached_at frame id slot layout bound) place live
  unfold PlaceMachine.localToOp PlaceMachine.localToOpCore
  simp only [bind,Bind.bind,EStateM.bind]
  rw [lay]
  simp [MachineHooks.currentFrame,LocalUnit.current,Stack.currentFrame?,operand,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]

theorem operand (s : Static) (metadata : Metadata s) (profile : Profile s) (capacity : 0 < s.capacity)
    (p : Packet) (tracker : MachineHooks.BorrowState) (destination : LocalDestination s p tracker)
    (amount : Size) (offset : destination.offset = some amount)
    (place : MemPlace Provenance) (indirect : destination.oldOperand = .indirect place)
    (older : Array LocalUnit.F) (original : p.before.stack.frames = older.push destination.caller)
    (bound : destination.localId < destination.caller.locals.size) :
    (ExecutionMachine.callHooks s.cfg s.limits).placeToOp () p.destination p.before =
      .ok ⟨.indirect (shifted place amount),s.abi.ret.layout⟩
        (LocalCachedPush.cachedState s p tracker destination older bound) := by
  have dictionaries := MetadataBinding.fields s metadata capacity
  obtain ⟨remaining,capacityEq⟩ : ∃ n : Nat, s.capacity = n+1 := ⟨s.capacity-1,by omega⟩
  have places := BodyPlaceDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes s.options
    (Configuration.leaves s.prepared s.options.place.debugAssertions) remaining metadata.construction s.cfg
    (by simpa only [Configuration.rootConfig,capacityEq] using s.built)
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
  have live : destination.slot.value = .live (.indirect place) := by rw [destination.live,indirect]
  have read := local_read s.cfg.compiler () older destination.caller p.before.machine destination.localId destination.slot
    destination.baseLayout place bound destination.slotAt live destination.cache computed
  let cached := LocalCachedPush.cachedState s p tracker destination older bound
  obtain ⟨context,projected,contextMemory⟩ := (FactoryProjection.fields s metadata capacity).projection cached
  have raw := source s metadata p tracker destination amount offset place indirect
  have queried : context.memoryOffset place amount .inbounds .none = .ok (shifted place amount) := by
    rw [contextMemory]
    exact (ProjectionSnapshot.offset_congr (ConcreteProtection.source s).pointers p.before cached rfl
      (fun _ => rfl) (fun _ => rfl) place amount .inbounds .none).trans raw
  have op : OpTy.offset context ⟨.indirect place,destination.baseLayout⟩ amount s.abi.ret.layout =
      .ok ⟨.indirect (shifted place amount),s.abi.ret.layout⟩ := by
    simp [OpTy.offset,OpTy.offsetWithMeta,metadata.unitSized,queried,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
  have before : p.before = LocalUnit.current older destination.caller p.before.machine := by
    cases stateEq : p.before with
    | mk stack machine => cases stack with | mk frames => simp_all [LocalUnit.current]
  have sourceBinding : (ExecutionMachine.callHooks s.cfg s.limits).placeToOp () p.destination =
      placeToOp s.cfg.projection.place () p.destination.toRuntimePlace := rfl
  rw [sourceBinding,places.projection,destination.encoding]
  simp only [offset,RuntimeStackPlace.toRuntimePlace,original,Array.size_push,Nat.add_sub_cancel]
  rw [before]
  unfold placeToOp placeToOpCore
  simp [ValidityMachine.placeHooks,ValidityMachine.compilerPolicy,PlaceMachine.placeHooks,
    Stack.frameIndex,LocalUnit.current,dictionaries.debug.trans profile.debug,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Except.pure,Except.bind]
  simp only [LocalUnit.current,ValidityMachine.compilerPolicy,dictionaries.debug.trans profile.debug] at read
  rw [read]
  change (do let context ← s.cfg.compiler.projection (); _)
    (cached) = _
  simp only [bind,Bind.bind,EStateM.bind,projected]
  rw [op]
  rfl
end EmptyFunction.ProjectedIndirectPreflight
