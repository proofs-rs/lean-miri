import duplicate_prefix.RootConstantStage
import duplicate_prefix.CanonicalConfigFacts
namespace DuplicatePrefix.LiteralConstant
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

noncomputable def evidence (site : CompilerConstantQueries.Site) :=
  (PreparedReflection.actual.compiler.constants.evidence.filter (·.site == site)).map (·.query)

open Lean Elab Tactic in
elab "simp_literal_source" : tactic => do
  let found := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith "Miri.Interpreter.constantType" then some (mkIdent name) else none
  let names := found.toArray
  evalTactic (← `(tactic| simp_all [CompilerConstantMachine.evalAtBound,
    ConstantMachine.fromCompiler,ConstantMachine.evalOperandWithLayout,
    evalConstOperandWithLayout,evalMirConstantWithLayout,constValueToOpWithLayout,
    ConstantQueries.valueQueries,MachineHooks.currentFrame,Storage.withCurrent,Stack.currentFrame?,
    bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,pure,EStateM.pure,
    Except.bind,Except.pure,evidence,$[$names:ident],*]))

/-- Source literal conversion composition. `convert` is discharged by checked
scalar-bit conversion or the actual immutable layout query in each client. -/
theorem at_bound
    (source : PreparedContracts.SourceComparator)
    (site : CompilerConstantQueries.Site) (literal : ConstValue) (ty : TyId) (refSpan : SpanRef)
    (known : Option LocalLayout) (immediate : Immediate Provenance) (layout : LocalLayout)
    (normalize : normalizationFromEvidence (evidence site) RootBody.reflected.functionInstance (.Val literal ty) = .ok (.Val literal ty))
    (convert : ∀ (queries : ConstantValueQueries Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
      (ConstantMachine.Context MiriMemoryKind Machine.RootUser))
      (state : ConstantState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
        (ConstantMachine.Context MiriMemoryKind Machine.RootUser)),
      valueToOpWithLayout PreparedReflection.actual.compiler.runtime queries literal ty known none state =
        .ok ⟨.immediate immediate,layout⟩ state)
    (functions : FunctionPointers.Hooks MiriMemoryKind Machine.RootUser Unit)
    (arithmetic : PointerArithmetic)
    (externStatic : DefId → MachineHooks.M MiriMemoryKind Machine.RootUser (Pointer Provenance))
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (bodyIndex : frame.bodyIdentity.index = site.bodyIndex)
    (location : frame.location = .mir site.location)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerConstantMachine.evalAtBound PreparedReflection.actual.compiler.constantBinding site
      functions arithmetic externStatic MemoryErrors.constant ⟨refSpan,none,.Val literal ty⟩ known none
      (Storage.withCurrent framesBefore frame machine) =
    .ok ⟨.immediate immediate,layout⟩ (Storage.withCurrent framesBefore frame machine) := by
  have compatible := RootCompilerFacts.constant_binding_compatible source
  simp_literal_source

theorem operand_at
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator) (debugOff : options.place.debugAssertions = false)
    (site : CompilerConstantQueries.Site) (path : OperandPath)
    (pathEq : site.path = (path.push (.field "constant")).map (fun element => match element with
      | .field name => CompilerConstantQueries.PathElement.field name
      | .index index => CompilerConstantQueries.PathElement.index index))
    (literal : ConstValue) (ty : TyId) (refSpan : SpanRef)
    (known : Option LocalLayout) (immediate : Immediate Provenance) (layout : LocalLayout)
    (normalize : normalizationFromEvidence (evidence site) RootBody.reflected.functionInstance (.Val literal ty) = .ok (.Val literal ty))
    (convert : ∀ (queries : ConstantValueQueries Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
      (ConstantMachine.Context MiriMemoryKind Machine.RootUser))
      (state : ConstantState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
        (ConstantMachine.Context MiriMemoryKind Machine.RootUser)),
      valueToOpWithLayout PreparedReflection.actual.compiler.runtime queries literal ty known none state =
        .ok ⟨.immediate immediate,layout⟩ state)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (bodyIndex : frame.bodyIdentity.index = site.bodyIndex)
    (location : frame.location = .mir site.location)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    OperandMachine.evalOperandAt
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation
        (PreparedContracts.actualConfig options () remaining span) limits))
      () path (.Constant ⟨refSpan,none,.Val literal ty⟩) known (Storage.withCurrent framesBefore frame machine) =
    .ok ⟨.immediate immediate,layout⟩ (Storage.withCurrent framesBefore frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent framesBefore frame machine
  obtain ⟨externStatic,constantAt⟩ := (CanonicalConfigFacts.actual_fields options () remaining span).constantAt debugOff
  have siteRead : CompilerOperandSites.current (path.push (.field "constant")) state = .ok site state := by
    cases site
    simp_all [CompilerOperandSites.current,MachineHooks.currentFrame,state,Storage.withCurrent,Stack.currentFrame?,
      bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,pure,EStateM.pure]
    rfl
  have result := at_bound source site literal ty refSpan known immediate layout normalize convert
    config.functions config.arithmetic externStatic framesBefore frame machine bodyIndex location callee
  change config.operands.constantAt () (path.push (.field "constant")) ⟨refSpan,none,.Val literal ty⟩ known state = _
  rw [constantAt]
  simpa only [siteRead,bind,EStateM.bind,pure,EStateM.pure] using result

#print axioms operand_at
#print axioms at_bound
end DuplicatePrefix.LiteralConstant
