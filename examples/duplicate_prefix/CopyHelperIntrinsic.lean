import duplicate_prefix.CopyHelperOperands
import duplicate_prefix.CopyHelperFacts
import duplicate_prefix.CopyIntrinsic
namespace DuplicatePrefix.CopyHelperIntrinsic
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem actual_operand_reduction
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (source dest : Scalar Provenance) (n : UInt64)
    (valid14 : (14 : MIR.LocalId) < frame.locals.size)
    (valid15 : (15 : MIR.LocalId) < frame.locals.size)
    (valid16 : (16 : MIR.LocalId) < frame.locals.size)
    (live14 : frame.locals[14].value = .live (.immediate (.scalar source)))
    (live15 : frame.locals[15].value = .live (.immediate (.scalar dest)))
    (live16 : frame.locals[16].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (cache14 : frame.locals[14].layout = some CopyCompilerFacts.sourcePointerLayout)
    (cache15 : frame.locals[15].layout = some CopyCompilerFacts.destPointerLayout)
    (cache16 : frame.locals[16].layout = some RootCompilerFacts.usizeLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) :
    let config := PreparedContracts.actualConfig options () remaining span
    let bound := ExecutionMachine.withValidation config limits
    (ExecutionMachine.stepHooks config limits).intrinsic ()
      (.CopyNonOverlapping ⟨.Move ⟨14,#[]⟩, .Move ⟨15,#[]⟩, .Move ⟨16,#[]⟩⟩)
      (Storage.withCurrent frames frame machine) =
    MachineHooks.run (Intrinsics.copyWith (CopyIntrinsic.statementMemory bound) ()
      ⟨.immediate (.scalar source),CopyCompilerFacts.sourcePointerLayout⟩
      ⟨.immediate (.scalar dest),CopyCompilerFacts.destPointerLayout⟩
      ⟨.immediate (.scalar (.fromScalarInt (.ofUInt64 n))),RootCompilerFacts.usizeLayout⟩ true)
      (Storage.withCurrent frames frame machine) := by
  dsimp only
  rw [CopyIntrinsic.statement_memory_source]
  unfold MachineHooks.run Call.run
  rw [CopyIntrinsic.nondiverging_copy_operands]
  · exact CopyHelperOperands.move_cached_local options limits remaining span debugOff frames frame machine
      14 (.scalar source) CopyCompilerFacts.sourcePointerLayout (OperandPath.instruction "src") none
      valid14 live14 cache14 (by decide +kernel) noClocks ghost
  · exact CopyHelperOperands.move_cached_local options limits remaining span debugOff frames frame machine
      15 (.scalar dest) CopyCompilerFacts.destPointerLayout (OperandPath.instruction "dst") none
      valid15 live15 cache15 (by decide +kernel) noClocks ghost
  · exact CopyHelperOperands.move_cached_local options limits remaining span debugOff frames frame machine
      16 (.scalar (.fromScalarInt (.ofUInt64 n))) RootCompilerFacts.usizeLayout (OperandPath.instruction "count") none
      valid16 live16 cache16 (by decide +kernel) noClocks ghost

theorem actual_generic_copy
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (source dest : Pointer Provenance) (n : UInt64)
    (valid14 : (14 : MIR.LocalId) < frame.locals.size)
    (valid15 : (15 : MIR.LocalId) < frame.locals.size)
    (valid16 : (16 : MIR.LocalId) < frame.locals.size)
    (live14 : frame.locals[14].value = .live (.immediate (.scalar (Scalar.fromPointer (PreparedContracts.actualConfig options () remaining span).access.runtime.base source))))
    (live15 : frame.locals[15].value = .live (.immediate (.scalar (Scalar.fromPointer (PreparedContracts.actualConfig options () remaining span).access.runtime.base dest))))
    (live16 : frame.locals[16].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (cache14 : frame.locals[14].layout = some CopyCompilerFacts.sourcePointerLayout)
    (cache15 : frame.locals[15].layout = some CopyCompilerFacts.destPointerLayout)
    (cache16 : frame.locals[16].layout = some RootCompilerFacts.usizeLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (bounded : n ≤ (PreparedContracts.actualConfig options () remaining span).projection.maxSizeOfVal.bytes) :
    let config := PreparedContracts.actualConfig options () remaining span
    ∃ pointers : CanonicalConfigFacts.RootPointers,
      config.arithmetic = pointers.arithmetic ∧
      config.access.resolvePointer = TypedMemoryProviders.resolvePointer pointers ∧
      (ExecutionMachine.stepHooks config limits).intrinsic ()
        (.CopyNonOverlapping ⟨.Move ⟨14,#[]⟩, .Move ⟨15,#[]⟩, .Move ⟨16,#[]⟩⟩)
        (Storage.withCurrent frames frame machine) =
      MachineHooks.run (GlobalMemoryCopyMachine.genericCopy config.access PointerMachine.User.addresses
        pointers.arithmetic source.withOptionalProvenance dest.withOptionalProvenance (Size.ofBytes n) 1 true)
        (Storage.withCurrent frames frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let bound := ExecutionMachine.withValidation config limits
  let state := Storage.withCurrent frames frame machine
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨pointers, arithmetic, resolve, alignment⟩ := fields.atomicPointerSource
  refine ⟨pointers, arithmetic, resolve, ?_⟩
  have sourceRead := CopyHelperOperands.move_cached_local options limits remaining span debugOff frames frame machine
    14 (.scalar (Scalar.fromPointer config.access.runtime.base source)) CopyCompilerFacts.sourcePointerLayout
    (OperandPath.instruction "src") none valid14 live14 cache14 (by decide +kernel) noClocks ghost
  have destRead := CopyHelperOperands.move_cached_local options limits remaining span debugOff frames frame machine
    15 (.scalar (Scalar.fromPointer config.access.runtime.base dest)) CopyCompilerFacts.destPointerLayout
    (OperandPath.instruction "dst") none valid15 live15 cache15 (by decide +kernel) noClocks ghost
  have countRead := CopyHelperOperands.move_cached_local options limits remaining span debugOff frames frame machine
    16 (.scalar (.fromScalarInt (.ofUInt64 n))) RootCompilerFacts.usizeLayout
    (OperandPath.instruction "count") none valid16 live16 cache16 (by decide +kernel) noClocks ghost
  have pointee : (CopyIntrinsic.statementMemory bound).pointeeType () CopyCompilerFacts.sourcePointerLayout.ty state = .ok 1 state := by
    have sourceTy : CopyCompilerFacts.sourcePointerLayout.ty = 9 := by decide +kernel
    unfold CopyIntrinsic.statementMemory
    dsimp only
    change (do
      let some pointee ← config.casts.builtinDeref () CopyCompilerFacts.sourcePointerLayout.ty true
        | throw (StepError.invalidProgram "copy intrinsic requires a pointer type")
      pure pointee) state = _
    rw [sourceTy, fields.castDeref]
    have deref : CompilerFacts.builtinDeref PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context 9 true = .ok (some 1) :=
      RootMetadataQueries.source_pointer_pointee
    simp only [bind, EStateM.bind, deref, pure, EStateM.pure]
  have byteQuery : bound.casts.layoutOf () 1 state = .ok CopyCompilerFacts.byteLayout state := by
    change config.casts.layoutOf () 1 state = _
    rw [fields.castLayout]
    simp only [CopyCompilerFacts.compiler_byte_layout]
  obtain ⟨sp, sr, sourceRepr⟩ := CopyCompilerFacts.initialized_scalar_exists
    CopyCompilerFacts.sourcePointerLayout CopyCompilerFacts.primitive_layouts_initialized.2.1
  obtain ⟨dp, dr, destRepr⟩ := CopyCompilerFacts.initialized_scalar_exists
    CopyCompilerFacts.destPointerLayout CopyCompilerFacts.primitive_layouts_initialized.2.2.1
  obtain ⟨cp, cr, countRepr⟩ := CopyCompilerFacts.initialized_scalar_exists
    RootCompilerFacts.usizeLayout CopyCompilerFacts.primitive_layouts_initialized.2.2.2
  exact CopyIntrinsic.statement_copy_reduction config limits bound rfl pointers () state
    ⟨.Move ⟨14,#[]⟩, .Move ⟨15,#[]⟩, .Move ⟨16,#[]⟩⟩ source dest n
    CopyCompilerFacts.sourcePointerLayout CopyCompilerFacts.destPointerLayout RootCompilerFacts.usizeLayout
    CopyCompilerFacts.byteLayout 1 sp dp cp sr dr cr sourceRepr destRepr countRepr
    (CanonicalConfigFacts.actual_retain_touched options () remaining span)
    (by change config.access.runtime.base.pointerWidth.bits = 64
        rw [CanonicalConfigFacts.actual_target_width options () remaining span]; rfl)
    pointee byteQuery CopyCompilerFacts.byte_layout_shape.2.1 CopyCompilerFacts.byte_layout_shape.2.2
    bounded fields.addresses arithmetic alignment sourceRead destRead countRead

#print axioms actual_operand_reduction
open Lean Elab Command in
run_cmd do
  for declaration in [``actual_operand_reduction, ``actual_generic_copy] do
   for dependency in (← collectAxioms declaration) do
     unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
       throwError "unapproved axiom {dependency}"
end DuplicatePrefix.CopyHelperIntrinsic
