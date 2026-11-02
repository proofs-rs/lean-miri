import duplicate_prefix.CopyPreconditions
import duplicate_prefix.CallEntryFacts

/-! Immutable source-call metadata for the two actual Miri language-UB guard
functions. Callers/callees are selected by canonical body/block identities. -/
namespace DuplicatePrefix.GuardCompilerFacts
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
open CopyPreconditions
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

private def checkedOk {Error Value : Type} :
    (result : Except Error Value) → result.isOk = true → Value
  | .ok value, _ => value
  | .error _, impossible => False.elim (by cases impossible)
private theorem checkedOk_eq {Error Value : Type} (result : Except Error Value) (supported : result.isOk = true) :
    result = .ok (checkedOk result supported) := by
  cases result with
  | ok value => rfl
  | error reason => cases supported

def languageCallQuery := CallResolution.atSite PreparedReflection.actual.compiler.lifecycle.calls.calls
  ⟨Bodies.copyWrapper.loaded.identity.index,0⟩
def runtimeCallQuery := CallResolution.atSite PreparedReflection.actual.compiler.lifecycle.calls.calls
  ⟨Bodies.checkLanguage.loaded.identity.index,0⟩
theorem language_site_supported : languageCallQuery.isOk = true := by decide +kernel
theorem runtime_site_supported : runtimeCallQuery.isOk = true := by decide +kernel

def languageCall := checkedOk languageCallQuery language_site_supported
def runtimeCall := checkedOk runtimeCallQuery runtime_site_supported

theorem language_call_eq : languageCallQuery = .ok languageCall := checkedOk_eq _ _
theorem runtime_call_eq : runtimeCallQuery = .ok runtimeCall := checkedOk_eq _ _
theorem language_callee : languageCall.callee = Bodies.checkLanguage.fnInstance := by with_unfolding_all rfl
theorem runtime_callee : runtimeCall.callee = Bodies.languageRuntime.fnInstance := by with_unfolding_all rfl

def abiQuery (callee : CallInstance) := CompilerInstanceAbi.abiOfInstance
  PreparedReflection.actual.compiler.lifecycle.instances callee #[]
def bodyQuery (callee : CallInstance) := CallResolution.loadedBodyOfInstance
  PreparedReflection.actual.compiler.lifecycle.calls.calls callee

theorem language_abi_supported : (abiQuery languageCall.callee).isOk = true := by decide +kernel
theorem runtime_abi_supported : (abiQuery runtimeCall.callee).isOk = true := by decide +kernel

def languageAbi := checkedOk (abiQuery languageCall.callee) language_abi_supported
def runtimeAbi := checkedOk (abiQuery runtimeCall.callee) runtime_abi_supported

theorem language_abi_eq : abiQuery languageCall.callee = .ok languageAbi := checkedOk_eq _ _
theorem runtime_abi_eq : abiQuery runtimeCall.callee = .ok runtimeAbi := checkedOk_eq _ _
theorem language_body_eq : bodyQuery languageCall.callee = .ok Bodies.checkLanguage.loaded := by with_unfolding_all rfl
theorem runtime_body_eq : bodyQuery runtimeCall.callee = .ok Bodies.languageRuntime.loaded := by with_unfolding_all rfl

theorem language_abi_shape :
    (languageAbi.args.map (·.layout.ty),languageAbi.ret.layout.ty,languageAbi.fixedCount.toNat,
      languageAbi.cVariadic,languageAbi.conv,languageAbi.canUnwind) = ( #[],0,0,false,.Rust,true) := by decide +kernel

theorem runtime_abi_shape :
    (runtimeAbi.args.map (·.layout.ty),runtimeAbi.ret.layout.ty,runtimeAbi.fixedCount.toNat,
      runtimeAbi.cVariadic,runtimeAbi.conv,runtimeAbi.canUnwind) = ( #[],0,0,false,.Rust,true) := by decide +kernel

theorem abi_return_layouts : languageAbi.ret.layout = RootCompilerFacts.boolLayout ∧
    runtimeAbi.ret.layout = RootCompilerFacts.boolLayout := by
  constructor <;> with_unfolding_all rfl

theorem call_site_abis : languageCall.abi = .ok languageAbi ∧ runtimeCall.abi = .ok runtimeAbi := by
  constructor <;> with_unfolding_all rfl

theorem source_body_shapes :
    Bodies.checkLanguage.loaded.body.argumentCount = 0 ∧
    Bodies.checkLanguage.loaded.body.locals = #[0,0,2] ∧
    Bodies.languageRuntime.loaded.body.argumentCount = 0 ∧
    Bodies.languageRuntime.loaded.body.locals = #[0] := by exact ⟨rfl,rfl,rfl,rfl⟩

theorem language_caller_location : CompilerRuntimeQueries.requiresCallerLocation
    PreparedReflection.actual.compiler.lifecycle.calls.runtime languageCall.callee = .ok false := by with_unfolding_all rfl
theorem runtime_caller_location : CompilerRuntimeQueries.requiresCallerLocation
    PreparedReflection.actual.compiler.lifecycle.calls.runtime runtimeCall.callee = .ok false := by with_unfolding_all rfl

theorem language_target_features : CompilerTargetFeatures.required
    PreparedReflection.actual.compiler.intrinsics languageCall.callee = .ok #[] := by with_unfolding_all rfl
theorem runtime_target_features : CompilerTargetFeatures.required
    PreparedReflection.actual.compiler.intrinsics runtimeCall.callee = .ok #[] := by with_unfolding_all rfl

theorem language_not_closure : CompilerCallFacts.isClosureLike
    PreparedReflection.actual.compiler.intrinsics languageCall.callee = .ok false := by with_unfolding_all rfl
theorem runtime_not_closure : CompilerCallFacts.isClosureLike
    PreparedReflection.actual.compiler.intrinsics runtimeCall.callee = .ok false := by with_unfolding_all rfl

theorem language_always_live : CallMachine.alwaysLiveVarsAndTemps Bodies.checkLanguage.loaded.body = .ok #[] := by with_unfolding_all rfl
theorem runtime_always_live : CallMachine.alwaysLiveVarsAndTemps Bodies.languageRuntime.loaded.body = .ok #[] := by with_unfolding_all rfl

theorem actual_language_abi (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (PreparedContracts.actualConfig options choice remaining span).calls.compiler.fnAbiOfInstance
      choice languageCall.callee #[] state = .ok languageAbi state := by
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).callCompiler]
  with_unfolding_all change (match abiQuery languageCall.callee with
    | .ok value => pure value
    | .error reason => throw (StepError.unsupported reason) : MachineHooks.M MiriMemoryKind Machine.RootUser (FnAbi MIR.TyId)) state = _
  rw [language_abi_eq]
  rfl

theorem actual_runtime_abi (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (PreparedContracts.actualConfig options choice remaining span).calls.compiler.fnAbiOfInstance
      choice runtimeCall.callee #[] state = .ok runtimeAbi state := by
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).callCompiler]
  with_unfolding_all change (match abiQuery runtimeCall.callee with
    | .ok value => pure value
    | .error reason => throw (StepError.unsupported reason) : MachineHooks.M MiriMemoryKind Machine.RootUser (FnAbi MIR.TyId)) state = _
  rw [runtime_abi_eq]
  rfl

theorem actual_language_load (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (PreparedContracts.actualConfig options choice remaining span).helpers.loadMir choice languageCall.callee state =
      .ok Bodies.checkLanguage.loaded state := by
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).loadMir]
  with_unfolding_all change (match bodyQuery languageCall.callee with
    | .ok value => pure value
    | .error reason => throw (StepError.unsupported s!"compiler call pipeline: {reason}") : MachineHooks.M MiriMemoryKind Machine.RootUser LoadedBody) state = _
  rw [language_body_eq]
  rfl

theorem actual_runtime_load (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (PreparedContracts.actualConfig options choice remaining span).helpers.loadMir choice runtimeCall.callee state =
      .ok Bodies.languageRuntime.loaded state := by
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).loadMir]
  with_unfolding_all change (match bodyQuery runtimeCall.callee with
    | .ok value => pure value
    | .error reason => throw (StepError.unsupported s!"compiler call pipeline: {reason}") : MachineHooks.M MiriMemoryKind Machine.RootUser LoadedBody) state = _
  rw [runtime_body_eq]
  rfl

def preambleQuery (body : LoadedBody) : Except String MIR.SpanRef := do
  let some entry := PreparedReflection.actual.compiler.lifecycle.lifecycle.entries[body.identity.index]?
    | throw "body lifecycle evidence absent"
  entry.preamble

theorem language_preamble_supported : (preambleQuery Bodies.checkLanguage.loaded).isOk = true := by decide +kernel
theorem runtime_preamble_supported : (preambleQuery Bodies.languageRuntime.loaded).isOk = true := by decide +kernel

def languagePreamble := checkedOk (preambleQuery Bodies.checkLanguage.loaded) language_preamble_supported
def runtimePreamble := checkedOk (preambleQuery Bodies.languageRuntime.loaded) runtime_preamble_supported

theorem language_preamble : CompilerLifecycle.preambleSpan
    PreparedReflection.actual.compiler.lifecycle.lifecycle Bodies.checkLanguage.loaded =
      (pure languagePreamble : MachineHooks.M MiriMemoryKind Machine.RootUser MIR.SpanRef) := by
  with_unfolding_all rfl

theorem runtime_preamble : CompilerLifecycle.preambleSpan
    PreparedReflection.actual.compiler.lifecycle.lifecycle Bodies.languageRuntime.loaded =
      (pure runtimePreamble : MachineHooks.M MiriMemoryKind Machine.RootUser MIR.SpanRef) := by
  with_unfolding_all rfl

theorem language_required_constants
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (identity : frame.bodyIdentity = Bodies.checkLanguage.loaded.identity)
    (callee : frame.functionInstance = Bodies.checkLanguage.fnInstance) :
    CompilerLifecycle.requiredConstants PreparedReflection.actual.compiler.lifecycle.lifecycle
      Bodies.checkLanguage.loaded (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore frame machine) := by
  with_unfolding_all change ((do
    let frame ← MachineHooks.currentFrame
    unless frame.bodyIdentity == Bodies.checkLanguage.loaded.identity &&
      frame.functionInstance == Bodies.checkLanguage.fnInstance do
      throw (StepError.invalidProgram "required-constant current frame identity/instance mismatch")
    pure () : MachineHooks.M MiriMemoryKind Machine.RootUser Unit)
      (Storage.withCurrent framesBefore frame machine)) = _
  simp only [MachineHooks.currentFrame, Storage.withCurrent, Stack.currentFrame?, Array.back?_push,
    Bind.bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, Pure.pure, EStateM.pure, identity, callee]
  with_unfolding_all rfl

theorem runtime_required_constants
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (identity : frame.bodyIdentity = Bodies.languageRuntime.loaded.identity)
    (callee : frame.functionInstance = Bodies.languageRuntime.fnInstance) :
    CompilerLifecycle.requiredConstants PreparedReflection.actual.compiler.lifecycle.lifecycle
      Bodies.languageRuntime.loaded (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore frame machine) := by
  with_unfolding_all change ((do
    let frame ← MachineHooks.currentFrame
    unless frame.bodyIdentity == Bodies.languageRuntime.loaded.identity &&
      frame.functionInstance == Bodies.languageRuntime.fnInstance do
      throw (StepError.invalidProgram "required-constant current frame identity/instance mismatch")
    pure () : MachineHooks.M MiriMemoryKind Machine.RootUser Unit)
      (Storage.withCurrent framesBefore frame machine)) = _
  simp only [MachineHooks.currentFrame, Storage.withCurrent, Stack.currentFrame?, Array.back?_push,
    Bind.bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, Pure.pure, EStateM.pure, identity, callee]
  with_unfolding_all rfl

theorem actual_language_caller_location (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits) (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options choice remaining span) limits).requiresCallerLocation
      languageCall.callee state = .ok false state := by
  change (PreparedContracts.actualConfig options choice remaining span).virtual.compiler.requiresCallerLocation
    languageCall.callee state = _
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).virtualCompiler]
  with_unfolding_all change (match CompilerRuntimeQueries.requiresCallerLocation
      PreparedReflection.actual.compiler.lifecycle.calls.runtime languageCall.callee with
    | .ok value => pure value
    | .error reason => throw (StepError.unsupported s!"compiler virtual query: {reason}") :
      MachineHooks.M MiriMemoryKind Machine.RootUser Bool) state = _
  rw [language_caller_location]
  rfl

theorem actual_language_target_features (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits) (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options choice remaining span) limits).checkTargetFeatures
      choice languageCall.callee state = .ok () state := by
  change ExecutionCallLeaves.checkTargetFeatures
    (PreparedContracts.actualConfig options choice remaining span).calls.compiler.targetFeatures languageCall.callee state = _
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).callCompiler]
  have query : (CompilerCallConstruction.compiler (C := Unit) PreparedReflection.actual.compiler
      options.compatibilityBudget).targetFeatures.required languageCall.callee =
      (pure #[] : MachineHooks.M MiriMemoryKind Machine.RootUser (Array ExecutionCallLeaves.TargetFeature)) := by
    with_unfolding_all change (match CompilerTargetFeatures.required PreparedReflection.actual.compiler.intrinsics
        languageCall.callee with
      | .ok value => pure value
      | .error reason => throw (StepError.unsupported reason) :
        MachineHooks.M MiriMemoryKind Machine.RootUser (Array ExecutionCallLeaves.TargetFeature)) = _
    rw [language_target_features]
  unfold ExecutionCallLeaves.checkTargetFeatures
  rw [query]
  rfl

theorem actual_language_noncapturing (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits) (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options choice remaining span) limits).nonCapturingClosure
      choice languageCall.callee languageAbi state = .ok false state := by
  change ExecutionCallLeaves.nonCapturingClosure (PreparedContracts.actualConfig options choice remaining span).calls.compiler
    languageCall.callee languageAbi state = _
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).callCompiler]
  have query : (CompilerCallConstruction.compiler (C := Unit) PreparedReflection.actual.compiler
      options.compatibilityBudget).isClosureLike languageCall.callee =
      (pure false : MachineHooks.M MiriMemoryKind Machine.RootUser Bool) := by
    with_unfolding_all change (match CompilerCallFacts.isClosureLike PreparedReflection.actual.compiler.intrinsics languageCall.callee with
      | .ok value => pure value
      | .error reason => throw (StepError.unsupported reason) : MachineHooks.M MiriMemoryKind Machine.RootUser Bool) = _
    rw [language_not_closure]
  unfold ExecutionCallLeaves.nonCapturingClosure
  rw [query]
  rfl

theorem language_return_compat {State : Type} (queries : LayoutCompat.Queries MIR.TyId State)
    (budget : Nat) (state : State) :
    LayoutCompat.checkArgumentCompat queries budget languageAbi.ret languageAbi.ret state = .ok true state := by
  with_unfolding_all rfl

theorem actual_runtime_caller_location (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits) (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options choice remaining span) limits).requiresCallerLocation
      runtimeCall.callee state = .ok false state := by
  change (PreparedContracts.actualConfig options choice remaining span).virtual.compiler.requiresCallerLocation
    runtimeCall.callee state = _
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).virtualCompiler]
  with_unfolding_all change (match CompilerRuntimeQueries.requiresCallerLocation
      PreparedReflection.actual.compiler.lifecycle.calls.runtime runtimeCall.callee with
    | .ok value => pure value
    | .error reason => throw (StepError.unsupported s!"compiler virtual query: {reason}") :
      MachineHooks.M MiriMemoryKind Machine.RootUser Bool) state = _
  rw [runtime_caller_location]
  rfl

theorem actual_runtime_target_features (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits) (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options choice remaining span) limits).checkTargetFeatures
      choice runtimeCall.callee state = .ok () state := by
  change ExecutionCallLeaves.checkTargetFeatures
    (PreparedContracts.actualConfig options choice remaining span).calls.compiler.targetFeatures runtimeCall.callee state = _
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).callCompiler]
  have query : (CompilerCallConstruction.compiler (C := Unit) PreparedReflection.actual.compiler
      options.compatibilityBudget).targetFeatures.required runtimeCall.callee =
      (pure #[] : MachineHooks.M MiriMemoryKind Machine.RootUser (Array ExecutionCallLeaves.TargetFeature)) := by
    with_unfolding_all change (match CompilerTargetFeatures.required PreparedReflection.actual.compiler.intrinsics
        runtimeCall.callee with
      | .ok value => pure value
      | .error reason => throw (StepError.unsupported reason) :
        MachineHooks.M MiriMemoryKind Machine.RootUser (Array ExecutionCallLeaves.TargetFeature)) = _
    rw [runtime_target_features]
  unfold ExecutionCallLeaves.checkTargetFeatures
  rw [query]
  rfl

theorem actual_runtime_noncapturing (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits) (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options choice remaining span) limits).nonCapturingClosure
      choice runtimeCall.callee runtimeAbi state = .ok false state := by
  change ExecutionCallLeaves.nonCapturingClosure (PreparedContracts.actualConfig options choice remaining span).calls.compiler
    runtimeCall.callee runtimeAbi state = _
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).callCompiler]
  have query : (CompilerCallConstruction.compiler (C := Unit) PreparedReflection.actual.compiler
      options.compatibilityBudget).isClosureLike runtimeCall.callee =
      (pure false : MachineHooks.M MiriMemoryKind Machine.RootUser Bool) := by
    with_unfolding_all change (match CompilerCallFacts.isClosureLike PreparedReflection.actual.compiler.intrinsics runtimeCall.callee with
      | .ok value => pure value
      | .error reason => throw (StepError.unsupported reason) : MachineHooks.M MiriMemoryKind Machine.RootUser Bool) = _
    rw [runtime_not_closure]
  unfold ExecutionCallLeaves.nonCapturingClosure
  rw [query]
  rfl

theorem runtime_return_compat {State : Type} (queries : LayoutCompat.Queries MIR.TyId State)
    (budget : Nat) (state : State) :
    LayoutCompat.checkArgumentCompat queries budget runtimeAbi.ret runtimeAbi.ret state = .ok true state := by
  with_unfolding_all rfl

#print axioms actual_language_caller_location
#print axioms actual_runtime_target_features
#print axioms actual_runtime_noncapturing
#print axioms actual_runtime_abi
#print axioms actual_runtime_load
#print axioms runtime_required_constants
#print axioms language_body_eq
#print axioms runtime_body_eq
#print axioms language_abi_shape
#print axioms runtime_abi_shape
#print axioms call_site_abis
end
end DuplicatePrefix.GuardCompilerFacts
