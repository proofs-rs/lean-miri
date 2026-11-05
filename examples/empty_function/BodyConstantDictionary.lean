import empty_function.CanonicalDictionaries

/-! Source equations of the canonical assignment dictionary. The existential
machine leaves remain the production leaves; no result of executing a memory
or interpreter operation is assumed here. -/
namespace EmptyFunction.BodyConstantDictionary
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

structure Fields (p : CompilerProviders.Prepared) (options : EvalConfigurationCore.Options)
    (config : Config) : Prop where
  constants : ∃ (functions : FunctionPointers.Hooks MiriMemoryKind RootUser Unit)
      (arithmetic : PointerArithmetic)
      (external : DefId → MachineHooks.M MiriMemoryKind RootUser (Pointer Provenance)),
    options.place.debugAssertions = false → config.operands.constantAt = fun _ path constant known => do
      let site ← CompilerOperandSites.current path
      CompilerConstantMachine.evalAtBound p.constantBinding site functions arithmetic external
        MemoryErrors.constant constant known none
def pointers (p : CompilerProviders.Prepared) (image : AllocationImage.Imported) (leaves : RootLeaves) :=
  (EvalPointerSource.make p image
    (EvalCoreMachine.extras leaves.sync ConcurrencyErrors.storeBuffer) leaves.pointerSource ()).pointers

def functions (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (options : EvalConfigurationCore.Options) (leaves : RootLeaves) :=
  EvalConfiguration.functions p image options.crossCrateInlineAlways (pointers p image leaves)

def external (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (options : EvalConfigurationCore.Options) (leaves : RootLeaves) :=
  CompilerExternStatic.resolve p.externStatics image
    (fun symbol => do
      let symbols ← match p.foreignSymbols with
        | .ok symbols => pure symbols
        | .error reason => throw (.unsupported s!"compiler foreign-symbol query: {reason}")
      match CompilerForeignSymbols.checkSymbolClash symbols symbol with
      | .ok () => pure ()
      | .error error => throw error)
    (functions p image options leaves)
    (fun user => EvalWorld.roots.externStatics (ExecutionStateTransport.toOuter user))

def constantAt (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (options : EvalConfigurationCore.Options) (leaves : RootLeaves) :
    Unit → OperandPath → ConstOperand → Option LocalLayout → MachineHooks.M MiriMemoryKind RootUser (OpTy Provenance) :=
  fun _ path constant known => do
    let site ← CompilerOperandSites.current path
    CompilerConstantMachine.evalAtBound p.constantBinding site (functions p image options leaves)
      (pointers p image leaves).arithmetic (external p image options leaves)
      MemoryErrors.constant constant known
      (if options.place.debugAssertions then some (fun left right =>
        match CompilerCovariance.compatible p options.place.debugAssertions left right with
        | .ok value => pure value | .error error => throw error) else none)

 theorem projected (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : RootLeaves) (remaining : Nat) (contract : Construction p)
    (debugOff : options.place.debugAssertions = false) :
    (EvalConfigurationCore.make p image bytes options leaves () (remaining + 1)).map
      (fun config => config.operands.constantAt) = .ok (constantAt p image options leaves) := by
  rw [EvalConfigurationCore.make_eq_context, EvalConfigurationCore.makeWithForeignContext]
  simp (config := {zeta := false}) only [contract.maximum_eq,
    EvalConfigurationCore.pureQuery_eq, EvalConfigurationCore.liftConstruction_eq,
    EvalMathMachine.hooks, CompilerCallConstruction.helpers,
    contract.i32_eq, contract.bool_eq, contract.u8_eq, contract.unit_eq, CompilerProviders.Prepared.rootSpan_eq, contract.rootSpan_eq,
    Except.mapError, Except.map, bind, Except.bind, pure, Except.pure]
  simp only [contract.maximum_eq, EvalConfigurationCore.pureQuery_eq,
    EvalConfigurationCore.liftConstruction_eq, EvalMathMachine.hooks, CompilerCallConstruction.helpers,
    contract.i32_eq, contract.bool_eq, contract.u8_eq, contract.unit_eq, CompilerProviders.Prepared.rootSpan_eq, contract.rootSpan_eq,
    Except.mapError, Except.map, bind, Except.bind, pure, Except.pure]
  apply congrArg Except.ok
  funext choice path constant known
  simp only [constantAt, debugOff, Bool.false_eq_true, ↓reduceIte]
  unfold functions pointers external
  rfl

 theorem fields_of_make (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : RootLeaves) (remaining : Nat) (contract : Construction p) (config : Config)
    (built : EvalConfigurationCore.make p image bytes options leaves () (remaining+1) = .ok config) :
    Fields p options config := by
  refine ⟨functions p image options leaves, (pointers p image leaves).arithmetic,
    external p image options leaves, ?_⟩
  intro debugOff
  have law := projected p image bytes options leaves remaining contract debugOff
  rw [built] at law
  have eq := Except.ok.inj law
  funext choice path constant known
  have point := congrFun (congrFun (congrFun (congrFun eq choice) path) constant) known
  simpa only [constantAt, debugOff, Bool.false_eq_true, ↓reduceIte] using point

end EmptyFunction.BodyConstantDictionary
