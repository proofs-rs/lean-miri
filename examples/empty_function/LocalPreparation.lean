import empty_function.InitializationPrefix
import empty_function.DispatcherSkeleton
import empty_function.LocalIndirectPreflight
import empty_function.ProjectedIndirectPreflight
import empty_function.ProjectedImmediatePreflight
namespace EmptyFunction.LocalPreparation
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-- All four caller-local shapes share an actual cache-only preflight. Unit
extraction of every enclosing immediate remains uninitialized; indirect values
keep their actual shifted pointer. No resource/choice condition is required. -/
theorem prepare (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (input : InputDraft.CurrentInputDraft s p)
    (destination : InputDraft.LocalDestination s p input.tracker) :
    ∃ (older : Array LocalUnit.F) (bound : destination.localId < destination.caller.locals.size)
      (operand : Operand Provenance),
      p.before.stack.frames = older.push destination.caller ∧
      (ExecutionMachine.callHooks s.cfg s.limits).placeToOp () p.destination p.before =
        .ok ⟨operand,s.abi.ret.layout⟩ (LocalCachedPush.cachedState s p input.tracker destination older bound) ∧
      (operand = .immediate .uninit ∨ ∃ place, operand = .indirect place) := by
  have capacity := InitializationPrefix.capacity_positive s
  obtain ⟨older,original⟩ := Array.back?_eq_some_iff.mp destination.current
  have bound : destination.localId < destination.caller.locals.size :=
    (Array.getElem?_eq_some_iff.mp destination.slotAt).1
  have sameCaller : destination.caller = input.caller :=
    Option.some.inj (destination.current.symm.trans input.current)
  have noClocks : destination.caller.extra.dataRace = none := by
    rw [sameCaller]; exact input.callerNoClocks
  cases DispatcherSkeleton.local_view destination with
  | wholeImmediate value whole old =>
    have layout : destination.baseLayout = s.abi.ret.layout :=
      (LocalPreflight.old_unit s metadata p input.tracker destination whole value old).1
    refine ⟨older,bound,.immediate .uninit,original,?_,Or.inl rfl⟩
    simpa only [LocalCachedPush.cachedState,layout] using
      LocalPreflight.operand s metadata profile capacity p input.tracker destination whole value old noClocks older original bound
  | wholeIndirect place whole old =>
    have layout : destination.baseLayout = s.abi.ret.layout := by
      cases destination
      cases whole
      assumption
    refine ⟨older,bound,.indirect place,original,?_,Or.inr ⟨place,rfl⟩⟩
    simpa only [LocalCachedPush.cachedState,layout] using
      LocalIndirectPreflight.operand s metadata profile capacity p input.tracker destination whole place old noClocks older original bound
  | projectedImmediate amount value offset old =>
    refine ⟨older,bound,.immediate .uninit,original,?_,Or.inl rfl⟩
    exact ProjectedImmediatePreflight.canonical s metadata profile capacity p input.tracker destination amount offset
      value old noClocks older original bound
  | projectedIndirect amount place offset old =>
    refine ⟨older,bound,.indirect (ProjectedIndirectPreflight.shifted place amount),original,?_,
      Or.inr ⟨_,rfl⟩⟩
    exact ProjectedIndirectPreflight.operand s metadata profile capacity p input.tracker destination amount offset
      place old older original bound

end EmptyFunction.LocalPreparation
