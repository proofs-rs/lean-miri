import empty_function.BodyStep
import empty_function.Configuration

/-! Unit validation leaves reduce to pure compiler facts. Runtime array
metadata is inspected but never changed. -/
namespace EmptyFunction.BodyQueries
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def leaves (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (projection : PlaceProjectionHooks Provenance (MachineHooks.State MiriMemoryKind RootUser) Unit MachineHooks.FrameExtra)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (EvalCoreMachine.Stored Unit Unit Unit Unit Unit Unit Unit Unit MinimalHost))) :=
  CompilerValidityLeaves.make p image EvalProjectionMachine.arrays projection pointers

 theorem local_layout (p : CompilerProviders.Prepared) (unit : LocalLayout)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (normalized : CompilerFrameContext.normalizedLocalType p
      (BodyStep.withUnit frame .uninit none) 0 = .ok unit.ty)
    (lookup : p.runtime.lookup unit.ty = .ok unit) :
    CompilerFrameContext.computeLocalLayout p 0
      (BodyStep.current frames (BodyStep.withUnit frame .uninit none) machine) =
      .ok unit (BodyStep.current frames (BodyStep.withUnit frame .uninit none) machine) := by
  unfold CompilerFrameContext.computeLocalLayout
  simp [MachineHooks.currentFrame, BodyStep.current, LocalUnit.current, Stack.currentFrame?,
    normalized, lookup, Except.mapError,
    get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure]
  simp_all!
  simp [pure, Pure.pure, EStateM.pure, lookup, Except.mapError]
  rfl

 theorem classifier (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (projection : PlaceProjectionHooks Provenance (MachineHooks.State MiriMemoryKind RootUser) Unit MachineHooks.FrameExtra)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (EvalCoreMachine.Stored Unit Unit Unit Unit Unit Unit Unit Unit MinimalHost)))
    (state : MachineHooks.State MiriMemoryKind RootUser) (ty : TyId)
    (notArray : state.machine.user.payload.payload.user.types.entries.any (·.value.ty == ty) = false)
    (kind : CompilerFactAdapters.validityKind p.lifecycle.calls.symbols.facts ty =
      .ok (.aggregate false false false)) :
    (leaves p image projection pointers).classify () ty state =
      .ok (.aggregate false false false) state := by
  simp [leaves, CompilerValidityLeaves.make, EvalProjectionMachine.arrays, notArray, kind,
    get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure, Except.mapError]
  rfl

 theorem type_name (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (projection : PlaceProjectionHooks Provenance (MachineHooks.State MiriMemoryKind RootUser) Unit MachineHooks.FrameExtra)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (EvalCoreMachine.Stored Unit Unit Unit Unit Unit Unit Unit Unit MinimalHost)))
    (state : MachineHooks.State MiriMemoryKind RootUser) (ty : TyId) (node : TypeNode)
    (found : p.lifecycle.calls.symbols.facts.context.runtime.node ty = .ok node) :
    (leaves p image projection pointers).typeName () ty state = .ok node.display state := by
  simp [leaves, CompilerValidityLeaves.make, found,
    get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure, Except.mapError]
  rfl

 theorem inhabited (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (projection : PlaceProjectionHooks Provenance (MachineHooks.State MiriMemoryKind RootUser) Unit MachineHooks.FrameExtra)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (EvalCoreMachine.Stored Unit Unit Unit Unit Unit Unit Unit Unit MinimalHost)))
    (state : MachineHooks.State MiriMemoryKind RootUser) (ty : TyId)
    (notArray : state.machine.user.payload.payload.user.types.entries.any (·.value.ty == ty) = false)
    (compatible : p.lifecycle.calls.symbols.facts.context.runtime.matchesSourceLeft
      state.machine.user.payload.payload.user.types.metadata.source.raw = true)
    (value : CompilerFacts.boolean p.lifecycle.calls.symbols.facts.context ty "opsem_inhabited" = .ok true) :
    (leaves p image projection pointers).opsemInhabited () ty state = .ok true state := by
  have absent : state.machine.user.payload.payload.user.types.entries.find? (·.value.ty == ty) = none := by
    apply Array.find?_eq_none.mpr
    exact Array.any_eq_false'.mp notArray
  simp [leaves, CompilerValidityLeaves.make, RuntimeArrayFacts.opsemInhabited,
    EvalProjectionMachine.arrays, absent, compatible, value,
    get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure, Except.mapError]
  rfl

 theorem adapter_classifier {P S C E Fn ABI Pad : Type}
    (facts : CompilerFactAdapters.Prepared) (base : ValidityVisitor.Hooks P S C E Fn ABI Pad)
    (choice : C) (state : S) (ty : TyId)
    (kind : CompilerFactAdapters.validityKind facts ty = .ok (.aggregate false false false)) :
    (CompilerFactAdapters.validityHooks facts base).classify choice ty state =
      .ok (.aggregate false false false) state := by
  simp [CompilerFactAdapters.validityHooks, kind, pure, Pure.pure, EStateM.pure]
  rfl

 theorem adapter_name {P S C E Fn ABI Pad : Type}
    (facts : CompilerFactAdapters.Prepared) (base : ValidityVisitor.Hooks P S C E Fn ABI Pad)
    (choice : C) (state : S) (ty : TyId) (node : TypeNode)
    (found : facts.context.runtime.node ty = .ok node) :
    (CompilerFactAdapters.validityHooks facts base).typeName choice ty state = .ok node.display state := by
  rw [CompilerFactAdapters.validity_typeName_of_node facts base choice ty node found]
  rfl

 theorem adapter_inhabited {P S C E Fn ABI Pad : Type}
    (facts : CompilerFactAdapters.Prepared) (base : ValidityVisitor.Hooks P S C E Fn ABI Pad)
    (choice : C) (state : S) (ty : TyId)
    (value : CompilerFacts.boolean facts.context ty "opsem_inhabited" = .ok true) :
    (CompilerFactAdapters.validityHooks facts base).opsemInhabited choice ty state = .ok true state := by
  simp [CompilerFactAdapters.validityHooks, value, pure, Pure.pure, EStateM.pure]
  rfl

end EmptyFunction.BodyQueries
