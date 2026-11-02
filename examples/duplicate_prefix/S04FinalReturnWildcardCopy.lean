import duplicate_prefix.S04FinalReturnRuleScalar
import duplicate_prefix.S04FinalReturnWildcardValidatedWrite
import duplicate_prefix.S04ProtectUninitWrite

namespace DuplicatePrefix.S04FinalReturnWildcardCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Actual configured copyReturn to the original wildcard memory destination.
Its permission and physical obligations are current local data; scalar copy,
live validity enforcement, ghost validation and provenance clearing all use
source hooks. There is no assumed copy or validation success. -/
theorem from_current {options : EvalConfigurationCore.Options} (limits : ExecutionMachine.Limits)
    {remaining : Nat} (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance)
    (input : S03PhysicalReturnInput.Input state.machine place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global)
    (distinct : input.entry.allocation.extra.roots.toList.Nodup)
    (short : input.entry.allocation.extra.nodes.size < 65536)
    (wildcard : input.pointer.provenance = .wildcard)
    (race : state.machine.dataRace = none)
    (backend : state.machine.user.payload.payload.user.backend = .none)
    (ghost : state.machine.user.payload.ghost = false)
    (shallow : state.machine.user.payload.validation = .Shallow)
    (sync : Array (Size × MemoryExtras.Entry Unit))
    (extras : state.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == input.id) =
      some (input.id,⟨none,sync⟩))
    (outside : ∀ row ∈ sync,
      row.1.bytes.toNat < input.offset.toNat ∨ input.offset.toNat + 1 ≤ row.1.bytes.toNat)
    (value : Bool) (fuel : Nat)
    (debugOff : options.place.debugAssertions = false)
    (validationFuel : options.limits.validation = fuel+1)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩) :
    ∃ updated, (GenericCallReturn.sourceControl
      (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyReturn ()
      ⟨.immediate (.scalar (Scalar.fromBool value)),RootCompilerFacts.boolLayout⟩ view state =
      (CanonicalCopy.replaceAllocation state input.id input.entry.kind updated,.ok ()) ∧
      updated.byteSize = input.entry.allocation.byteSize ∧
      updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let inner := PreparedContracts.actualConfig options () remaining span
  let bound := ExecutionMachine.withValidation config limits
  let hooks := (ExecutionMachine.projectionHooks bound).place
  let dest : RuntimePlace Provenance := ⟨.memory place.mplace,place.layout⟩
  let scalar : Immediate Provenance := .scalar (Scalar.fromBool value)
  obtain ⟨updated,combined,_,size,length,mutable⟩ := S04FinalReturnWildcardValidatedWrite.from_current
    (options := options) (remaining := remaining) span state place input runtime distinct short wildcard
    race backend ghost shallow sync extras outside value fuel
  obtain ⟨stored,write,_,_,_,_,_,_,_⟩ := S04FinalReturnWildcardWrite.from_current
    (options := options) (remaining := remaining) span state place input runtime distinct short wildcard
    race backend sync extras outside value
  let afterStore := CanonicalCopy.replaceAllocation state input.id input.entry.kind stored
  let after := CanonicalCopy.replaceAllocation state input.id input.entry.kind updated
  have physical : PlaceMachine.writeMemory config.access (fun _ => true) scalar place state = .ok () afterStore := by
    rw [S04FinalReturnRuleScalar.scalar_policy config.access place (Scalar.fromBool value)
      (fun _ => true) config.compiler.willValidateMemory]
    exact write
  have validated : ValidityMachine.validateRuntime inner.validity () (fuel+1) dest true afterStore = .ok () after := by
    simp only [Bind.bind,EStateM.bind] at combined
    rw [write] at combined
    exact combined
  have fields := CanonicalConfigFacts.actual_fields options () (remaining+1) span
  have noValidate : writePlaceImmediateNoValidate hooks () scalar dest state = .ok () afterStore := by
    unfold writePlaceImmediateNoValidate asMplaceOrMutableLocal
    have sized : place.layout.layout.isSized = true := by rw [input.layout]; decide +kernel
    simp only [dest,sized,bind,pure]
    change config.projection.place.writeMemoryNoValidate () scalar place state = _
    rw [fields.projectionWriteMemory]
    have accessGhost : config.access.ghostMode = false := by
      rw [(DuplicatePrefixPhysicalContexts.canonical options remaining span).outerAccessEq]
      rfl
    have scope := S04ProtectUninitWrite.scopedAccess_of_not_ghost config.access state accessGhost ghost
    dsimp only [config] at scope
    have enforce : ValidityMachine.enforceValidity state = .ok true state := by
      simp [ValidityMachine.enforceValidity,shallow,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
    simp only [bind,EStateM.bind,scope,enforce]
    exact physical
  have enforced : hooks.enforceValidity () place.layout afterStore = .ok true afterStore := by
    change config.projection.place.enforceValidity () place.layout afterStore = _
    rw [fields.projectionEnforce]
    simp [ValidityMachine.enforceValidity,afterStore,CanonicalCopy.replaceAllocation,shallow,
      get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
  have checked : hooks.validate () dest afterStore = .ok () after := by
    change config.projection.place.validate () dest afterStore = _
    rw [fields.projectionValidate,CanonicalConfigFacts.actual_validate_successor,validationFuel]
    exact validated
  have actualWrite : (ExecutionMachine.rvalueHooks config limits).writeImmediate () scalar dest state = .ok () after := by
    change writePlaceImmediate hooks () scalar dest state = _
    unfold writePlaceImmediate
    simp only [bind,EStateM.bind,noValidate]
    erw [enforced]
    exact checked
  have compatible : bound.copy.compatible = CompilerCovariance.compatible PreparedReflection.actual.compiler false := by
    change config.copy.compatible = _
    rw [fields.copyCompatible,debugOff]
  have destLayout : dest.layout = RootCompilerFacts.boolLayout := input.layout
  have flag := GenericCallReturn.same_layout_transmute_flag hooks bound.copy PreparedReflection.actual.compiler ()
    RootCompilerFacts.boolLayout scalar dest destLayout compatible
  have exactCopy : copyRuntimePlace hooks bound.copy () ⟨.immediate scalar,RootCompilerFacts.boolLayout⟩ dest true =
      (ExecutionMachine.rvalueHooks config limits).copyOp () ⟨.immediate scalar,RootCompilerFacts.boolLayout⟩ dest := by
    rw [flag]
    rfl
  obtain ⟨primitive,range,repr⟩ := CopyCompilerFacts.initialized_scalar_exists RootCompilerFacts.boolLayout
    RootGenericBoolWrite.bool_initialized
  have copy := ActualScalarCopy.actual_copy_scalar options limits (remaining+1) span debugOff
    RootCompilerFacts.boolLayout scalar dest destLayout _ repr RootGenericBoolWrite.bool_sized
  refine ⟨updated,?_,size,length,mutable⟩
  change MachineHooks.run (copyRuntimePlace hooks bound.copy ()
    ⟨.immediate scalar,RootCompilerFacts.boolLayout⟩ view.toRuntimePlace true) state = _
  rw [destination,exactCopy,copy]
  unfold MachineHooks.run Call.run
  rw [actualWrite]

end
end DuplicatePrefix.S04FinalReturnWildcardCopy
