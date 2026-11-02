import duplicate_prefix.AsMutPtrCastAssign
import duplicate_prefix.ImmediateReadProof
namespace DuplicatePrefix.RootPointerCast
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem thin_to_thin [PointerProvenance P]
    (hooks : CastHooks P S C V) (choice : C) (source target : LocalLayout)
    (value : Immediate P) (pointee : TyId)
    (sourceKind : hooks.typeInfo choice source.ty = pure (.rawPointer pointee))
    (targetKind : hooks.typeInfo choice target.ty = pure (.rawPointer pointee))
    (sameSize : source.layout.size = target.layout.size) :
    Cast.ptrToPtr hooks choice ⟨value,source⟩ target = pure ⟨value,target⟩ := by
  funext state
  unfold Cast.ptrToPtr
  unfold_internal ".Cast.isAnyPointer"
  simp [sourceKind,targetKind,sameSize,bind,EStateM.bind,pure,EStateM.pure]

theorem const_kind (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    (ExecutionMachine.castHooks (ExecutionMachine.withValidation
      (PreparedContracts.actualConfig options () remaining span) limits) limits).typeInfo () CopyCompilerFacts.sourcePointerLayout.ty =
    pure (.rawPointer 1) := by
  have ty : CopyCompilerFacts.sourcePointerLayout.ty = 9 := by with_unfolding_all rfl
  change (PreparedContracts.actualConfig options () remaining span).casts.typeInfo () _ = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).castTypeInfo,ty]
  funext state
  change (match CompilerFactAdapters.castTypeInfo PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts 9 with
    | .ok kind => EStateM.Result.ok kind state
    | .error reason => EStateM.Result.error (StepError.unsupported s!"cast compiler query: {reason}") state) = .ok (.rawPointer 1) state
  with_unfolding_all rfl

theorem to_write
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (value : Scalar Provenance) (destination : RuntimePlace Provenance)
    (layout : destination.layout = CopyCompilerFacts.sourcePointerLayout)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (shallow : state.machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () remaining span
    let hooks := ExecutionMachine.castHooks (ExecutionMachine.withValidation config limits) limits
    Cast.cast hooks () limits.casts ⟨.immediate (.scalar value),CopyCompilerFacts.destPointerLayout⟩
      .PtrToPtr 9 destination state = hooks.writeImmediate () (.scalar value) destination state := by
  let config := PreparedContracts.actualConfig options () remaining span
  let hooks := ExecutionMachine.castHooks (ExecutionMachine.withValidation config limits) limits
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have ty : CopyCompilerFacts.sourcePointerLayout.ty = 9 := by with_unfolding_all rfl
  have destLayout : hooks.destLayout destination = CopyCompilerFacts.sourcePointerLayout := layout
  have enforced : hooks.enforceValidity () CopyCompilerFacts.destPointerLayout state = .ok true state := by
    change config.compiler.enforceValidity () _ state = _
    rw [fields.compilerEnforce]
    simp [ValidityMachine.enforceValidity,shallow,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
  have sourceKind := AsMutPtrCast.actual_target_kind options limits remaining span
  have targetKind := const_kind options limits remaining span
  obtain ⟨primitive,range,reprEq⟩ := CopyCompilerFacts.initialized_scalar_exists
    CopyCompilerFacts.destPointerLayout CopyCompilerFacts.primitive_layouts_initialized.2.1
  have sourceRead := ImmediateReadProof.read_scalar_immediate config.access state value CopyCompilerFacts.destPointerLayout
    (CopyCompilerFacts.initialized_scalar_exists _ CopyCompilerFacts.primitive_layouts_initialized.2.1)
    (by rw [CanonicalConfigFacts.actual_retain_touched options () remaining span])
  have hooksRead : hooks.readImmediate () ⟨.immediate (.scalar value),CopyCompilerFacts.destPointerLayout⟩ state =
      .ok ⟨.scalar value,CopyCompilerFacts.destPointerLayout⟩ state := by
    exact sourceRead
  have pointerCast := thin_to_thin hooks () CopyCompilerFacts.destPointerLayout CopyCompilerFacts.sourcePointerLayout
    (.scalar value) 1 sourceKind targetKind (by decide +kernel)
  change Cast.cast hooks () limits.casts _ .PtrToPtr 9 destination state = _
  unfold Cast.cast
  simp only [destLayout,ty,beq_self_eq_true,↓reduceIte,bind,EStateM.bind,pure,EStateM.pure]
  simp only [Bool.false_eq_true,Bool.not_false,Bool.true_eq,↓reduceIte,bind,EStateM.bind,pure,EStateM.pure]
  rw [enforced]
  simp only [bind,EStateM.bind]
  rw [sourceKind]
  simp only [bind,EStateM.bind,pure,EStateM.pure,↓reduceIte]
  rw [reprEq]
  simp only [Bool.false_eq_true,ite_false,bind,EStateM.bind,pure,EStateM.pure]
  rw [hooksRead]
  simp only [bind,EStateM.bind,pure,EStateM.pure]
  erw [pointerCast]
  rfl

#print axioms thin_to_thin
#print axioms const_kind
#print axioms to_write
end DuplicatePrefix.RootPointerCast
