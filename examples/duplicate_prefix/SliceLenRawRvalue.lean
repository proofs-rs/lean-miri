import duplicate_prefix.SliceLenRawRetag
import duplicate_prefix.PtrMetadataComplete
import duplicate_prefix.ProjectionMetadataFacts
namespace DuplicatePrefix.SliceLenRawRvalue
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open PtrMetadataHelper PtrMetadataComplete
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def carrierPointer (carrier : Pointer Provenance ⊕ UInt64) : Pointer (Option Provenance) :=
  match carrier with
  | .inl pointer => pointer.withOptionalProvenance
  | .inr address => Pointer.withoutProvenance address

def carrierMemory (carrier : Pointer Provenance ⊕ UInt64) (len : UInt64) : MemPlace Provenance :=
  ⟨carrierPointer carrier,.metadata (.fromScalarInt (.ofUInt64 len)),none⟩

theorem carrier_to_ref (carrier : Pointer Provenance ⊕ UInt64) (target : TargetDataLayout) (len : UInt64)
    (width : target.pointerWidth = .w64) :
    (carrierMemory carrier len).toRef target = .ok (rawImmediate carrier target len) := by
  cases carrier with
  | inl pointer =>
    simp [carrierMemory,carrierPointer,MemPlace.toRef,Immediate.newPointerWithMeta,
      ScalarPointers.from_some_pointer,rawImmediate,RetagReferencePlace.sliceValue,bind,Except.bind,pure,Except.pure,Except.mapError]
  | inr address =>
    simp [carrierMemory,carrierPointer,MemPlace.toRef,Immediate.newPointerWithMeta,
      RetagReferencePlace.integer_from_pointer target address width,rawImmediate,RetagReferencePlace.integerSliceValue,
      bind,Except.bind,pure,Except.pure,Except.mapError]

theorem raw_staged_to_write
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (carrier : Pointer Provenance ⊕ UInt64) (len : UInt64) (baseRaw : Bool)
    (source dest : MIR.Place) (destValue : RuntimePlace Provenance)
    (state0 state1 : CanonicalConfigFacts.RootState)
    (destLayout : destValue.layout = rawLayout)
    (destination : (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits).evalPlace () dest true state0 = .ok destValue state1)
    (base : (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits).placeBaseRaw () source state1 = .ok baseRaw state1)
    (dereference : (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits).evalPlace () source false state1 =
      .ok ⟨.memory (carrierMemory carrier len),ProjectionMetadataFacts.sliceLayout⟩ state1) :
    let config := PreparedContracts.actualConfig options () remaining span
    let hooks := ExecutionMachine.rvalueHooks config limits
    evalRvalueIntoPlace hooks () (.RawPtr .Const source) dest state0 =
      hooks.writeImmediate () (rawImmediate carrier config.access.runtime.base len) destValue state1 := by
  let config := PreparedContracts.actualConfig options () remaining span
  let hooks := ExecutionMachine.rvalueHooks config limits
  let value : RvalueImmTy Provenance := ⟨rawImmediate carrier config.access.runtime.base len,rawLayout⟩
  have allocated : hooks.forceAllocation () ⟨.memory (carrierMemory carrier len),ProjectionMetadataFacts.sliceLayout⟩ state1 =
      .ok (carrierMemory carrier len) state1 := by
    rfl
  have reference : hooks.toRef () (carrierMemory carrier len) state1 = .ok value.imm state1 := by
    change (ExecutionMachine.rvalueHooks config limits).toRef () (carrierMemory carrier len) state1 = _
    unfold ExecutionMachine.rvalueHooks
    dsimp only
    unfold_internal ".ExecutionMachine.lift"
    rw [show (ExecutionMachine.withValidation config limits).access = config.access from rfl]
    rw [carrier_to_ref carrier config.access.runtime.base len (CanonicalConfigFacts.actual_target_width options () remaining span)]
    rfl
  have scopedRaw : hooks.withRetagMode () .Raw (do
      let result ← hooks.retagPtrValue () value value.layout.ty
      pure (result.getD value)) state1 = .ok value state1 := by
    change MachineHooks.withRetagMode .Raw (do
      let result ← TypedRetag.machineRetagPtrValue config.retag limits.retag value value.layout.ty
      pure (result.getD value)) state1 = _
    rw [show value.layout.ty = 154 from raw_layout_type]
    exact congrFun (SliceLenRawRetag.raw_scope_unchanged config.retag limits.retag value 154
      (SliceLenRawRetag.actual_raw_shape options remaining span)) state1
  have scopedRaw' : hooks.withRetagMode () .Raw
      (EStateM.bind (hooks.retagPtrValue () (⟨value.imm,rawLayout⟩ : RvalueImmTy Provenance) rawLayout.ty)
        (fun result => EStateM.pure (result.getD (⟨value.imm,rawLayout⟩ : RvalueImmTy Provenance)))) state1 =
      .ok value state1 := scopedRaw
  have base' : hooks.placeBaseRaw () source state1 = .ok baseRaw state1 := base
  have dereference' : hooks.evalPlace () source false state1 =
      .ok ⟨.memory (carrierMemory carrier len),ProjectionMetadataFacts.sliceLayout⟩ state1 := dereference
  change evalRvalueIntoPlace hooks () (.RawPtr .Const source) dest state0 = _
  unfold evalRvalueIntoPlace
  simp only [bind,EStateM.bind]
  rw [destination]
  simp only
  have placeLayout : hooks.placeLayout destValue = rawLayout := destLayout
  simp only [placeLayout]
  change (do
    let raw ← hooks.placeBaseRaw () source
    let src ← hooks.evalPlace () source false
    let src ← hooks.forceAllocation () src
    let imm ← hooks.toRef () src
    let val : RvalueImmTy Provenance := ⟨imm,rawLayout⟩
    let val ← if !raw && RawPtrKind.Const != RawPtrKind.FakeForPtrMetadata then
      hooks.withRetagMode () .Raw (do let result ← hooks.retagPtrValue () val val.layout.ty;pure (result.getD val))
      else pure val
    hooks.writeImmediate () val.imm destValue) state1 = _
  simp only [bind,EStateM.bind,base',dereference',allocated,reference]
  cases baseRaw <;> simp only [Bool.not_false,Bool.not_true,Bool.false_and,Bool.true_and,
    show (RawPtrKind.Const != RawPtrKind.FakeForPtrMetadata) = true by decide,ite_true,ite_false,
    scopedRaw',bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
  all_goals first | rfl | (rw [scopedRaw'];rfl)

#print axioms raw_staged_to_write
end
end DuplicatePrefix.SliceLenRawRvalue
