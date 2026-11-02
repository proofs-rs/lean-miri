import empty_function.Configuration
import Miri.Input.CompilerContextSpan
import Lean

/-! Field equations extracted from the canonical factory. Construction facts
are pure compiler queries; none depends on a runtime state or memory operation. -/
namespace EmptyFunction.CanonicalDictionaries
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
open EmptyFunction.Configuration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
abbrev Config := ExecutionMachine.Config MiriMemoryKind RootUser Unit Unit ABI.ExternAbi Unit
abbrev Stored := EvalCoreMachine.Stored Unit Unit Unit Unit Unit Unit Unit Unit MinimalHost
abbrev Pointers := PointerMachine.Hooks MiriMemoryKind (ValidityMachine.Control Stored)
abbrev Table := VTableHooks Provenance (MachineHooks.State MiriMemoryKind RootUser) Unit CallInstance (FnAbi MIR.TyId)
abbrev Globals := GlobalAllocationHooks Provenance TreeBorrows.BorrowTree MiriMemoryKind
  (PlaceMachine.AccessState MiriMemoryKind RootUser)

/-- Immutable compiler construction queries, with no runtime-state argument. -/
structure Construction (compiler : CompilerProviders.Prepared) where
  maximum : Size
  maximum_eq : CompilerExecutionBounds.maximum compiler.runtime.target = .ok maximum
  i32 : LocalLayout
  i32_eq : compiler.primitiveLayout "i32" = .ok i32
  bool : LocalLayout
  bool_eq : compiler.primitiveLayout "bool" = .ok bool
  u8 : LocalLayout
  u8_eq : compiler.primitiveLayout "u8" = .ok u8
  unit : LocalLayout
  unit_eq : compiler.primitiveLayout "unit" = .ok unit
  rootSpan : MIR.SpanRef
  rootSpan_eq : CompilerContextSpan.rootSpan compiler.program = .ok rootSpan

structure Fields (p : CompilerProviders.Prepared) (options : EvalConfigurationCore.Options)
    (config : Config) : Prop where
  construction : ∃ (pointers : Pointers) (table : Table) (globals : Globals),
    config.retag = EvalRetagMachine.hooks p.lifecycle.calls.symbols.facts p.lifecycle.calls.runtime
      (CompilerRetagOptions.make p options.retag) config.access config.projection table pointers () ∧
    config.access.resolvePointer = TypedMemoryProviders.resolvePointer pointers ∧
    pointers.ensureTreeExtra = GlobalAllocationMachine.ensure .global globals ∧
    globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}}
  precise : config.retag.preciseInteriorMut = pure options.retag.preciseInteriorMut
  implicit : config.retag.implicitWrites = pure options.retag.implicitWrites
  log : config.retag.logCreation = fun _ _ _ _ _ => pure ()
  typeFreeze : config.retag.typeIsFreeze = fun ty state =>
    match CompilerFacts.boolean p.lifecycle.calls.symbols.facts.context ty "is_freeze" with
    | .ok value => .ok value state
    | .error reason => .error (.unsupported reason) state
  retainTouched : config.access.retainTouched = fun machine _ => machine
  runtime : config.access.runtime = p.runtime.target
  arithmetic : config.arithmetic = ⟨p.runtime.target.pointerSize⟩
  validation : config.compiler.validationInProgress = ValidityMachine.validationInProgress
  debug : config.compiler.debugAssertions = options.place.debugAssertions
  debugAbi : options.place.debugAssertions = false → config.compiler.debugAbiCheck = fun _ _ => pure ()
  layout : config.compiler.layout = fun (_ : Unit) id => CompilerFrameContext.computeLocalLayout p id
  frameCompiler : config.lifecycle.compiler = CompilerFrameMetadata.hooks p.lifecycle.frames options.userRelevantCrates
  preambleSpan : config.lifecycle.preambleSpan = CompilerLifecycle.preambleSpan p.lifecycle.lifecycle
  requiredConstants : config.lifecycle.requiredConstants = CompilerLifecycle.requiredConstants p.lifecycle.lifecycle
  storageSized : config.lifecycle.storage.veryTriviallySized = CompilerStorage.veryTriviallySized p.runtime
  storageLayout : config.lifecycle.storage.layout = CompilerFrameContext.computeLocalLayout p
  callsCompiler : config.calls.compiler = CompilerExecutionCallLeaves.make p options.compatibilityBudget
  virtualCompiler : config.virtual.compiler = CompilerVirtualLeaves.make p.lifecycle.calls
  freshLocalsIdentity : config.lifecycle.freshLocalsIdentity = fun machine =>
    let (supply, label) := (EvalConfiguration.identity.get machine.user).allocate
    ({machine with user := EvalConfiguration.identity.put machine.user supply}, label)

/-- The actual factory succeeds from pure metadata facts and provides the
canonical retag dictionaries. Runtime memory and caller frames are arbitrary. -/
theorem make_fields (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : RootLeaves) (remaining : Nat) (contract : Construction p) :
    ∃ config : Config,
      EvalConfigurationCore.make p image bytes options leaves () (remaining + 1) = .ok config ∧
      Fields p options config := by
  rw [EvalConfigurationCore.make_eq_context, EvalConfigurationCore.makeWithForeignContext]
  simp (config := {zeta := false}) only [contract.maximum_eq,
    EvalConfigurationCore.pureQuery_eq, EvalConfigurationCore.liftConstruction_eq,
    EvalMathMachine.hooks, CompilerCallConstruction.helpers,
    contract.i32_eq, contract.bool_eq, contract.u8_eq, contract.unit_eq, contract.rootSpan_eq,
    Except.mapError, Except.map, bind, Except.bind, pure, Except.pure]
  refine ⟨_, rfl, ?_⟩
  constructor
  · with_unfolding_all exact ⟨_, _, _, rfl, rfl, rfl, rfl⟩
  all_goals try with_unfolding_all rfl
  case typeFreeze =>
    funext ty state
    cases h : CompilerFacts.boolean p.lifecycle.calls.symbols.facts.context ty "is_freeze" <;>
      simp only [EvalRetagMachine.hooks, h] <;> with_unfolding_all rfl
  case debugAbi =>
    intro debugOff
    with_unfolding_all simp only [EvalPlaceConstruction.compiler, debugOff, Bool.false_eq_true, ↓reduceIte]

/-- Recover the source dictionary equations for any successful canonical
factory result. The construction certificate contains only compiler facts. -/
theorem fields_of_make (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : RootLeaves) (remaining : Nat) (contract : Construction p) (config : Config)
    (built : EvalConfigurationCore.make p image bytes options leaves () (remaining+1) = .ok config) :
    Fields p options config := by
  obtain ⟨actual, equal, fields⟩ := make_fields p image bytes options leaves remaining contract
  have same : actual = config := Except.ok.inj (equal.symm.trans built)
  simpa only [same] using fields

/-- Sized layouts take the query-free dynamic-layout fast path. -/
theorem Fields.sizeAndAlign {p options config} (fields : Fields p options config)
    (place : MPlaceTy Provenance) (sized : place.layout.layout.isSized = true) :
    config.retag.sizeAndAlign place = pure (some (place.layout.layout.size, place.layout.layout.align.abi)) := by
  obtain ⟨pointers, table, globals, retag, _⟩ := fields.construction
  rw [retag]
  simp only [EvalRetagMachine.hooks]
  unfold DynamicLayout.sizeAndAlignFromMeta
  rw [sized]
  rfl

/-- Unit Freeze is a pure compiler fact, independent of the caller state. -/
theorem Fields.freeze {p options config} (fields : Fields p options config) (ty : MIR.TyId)
    (metadata : CompilerFacts.boolean p.lifecycle.calls.symbols.facts.context ty "is_freeze" = .ok true) :
    config.retag.typeIsFreeze ty = pure true := by
  rw [fields.typeFreeze]
  funext state
  simp only [metadata]
  rfl

/-- The source zero-byte access checker is fixed by the canonical factory. -/
theorem Fields.checkPtrAccess {p options config} (fields : Fields p options config) :
    config.retag.checkPtrAccess = ValidityMachine.checkPointerAccess config.access := by
  obtain ⟨pointers, table, globals, retag, _⟩ := fields.construction
  rw [retag]
  rfl

/-- Resolver/ensure dictionaries and their memory synchronization law share
one actual source pointer construction. -/
theorem Fields.pointerDictionaries {p options config} (fields : Fields p options config) :
    ∃ (pointers : Pointers) (globals : Globals),
      config.retag.resolveAllocation = TypedValidityProviders.resolveAllocation pointers ∧
      config.access.resolvePointer = TypedMemoryProviders.resolvePointer pointers ∧
      config.retag.ensureTreeExtra = GlobalAllocationMachine.ensure .global globals ∧
      globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}} := by
  obtain ⟨pointers, table, globals, retag, resolve, ensure, sync⟩ := fields.construction
  refine ⟨pointers, globals, ?_, resolve, ?_, sync⟩
  · rw [retag]; rfl
  · rw [retag]; exact ensure

/-- Uninitialization uses the real scoped access and memory writer. -/
theorem Fields.writeUninit {p options config} (fields : Fields p options config)
    (place : MPlaceTy Provenance) :
    config.retag.writeUninit place = (do
      let access ← ValidityMachine.scopedAccess config.access
      PlaceMachine.writeMemory access (fun _ => false) .uninit place) := by
  obtain ⟨pointers, table, globals, retag, _⟩ := fields.construction
  rw [retag]
  rfl

/-- The shared global source is fixed by the same actual factory, including
its current compiler image and host leaves. No existential global callback is
selected independently of the execution configuration. -/
abbrev pointerSource (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (leaves : RootLeaves) :=
  EvalPointerSource.make p image (EvalCoreMachine.extras leaves.sync ConcurrencyErrors.storeBuffer)
    leaves.pointerSource ()

abbrev globalLeaves (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (leaves : RootLeaves) : GlobalAllocationMachine.Leaves MiriMemoryKind RootUser where
  bytes := EvalPointerSource.bytes p image leaves.pointerSource (pointerSource p image leaves).address
  globalRootPointer := (pointerSource p image leaves).rootPointer
  diagnostic := fun _ _ _ => pure ()

structure GlobalFields (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (leaves : RootLeaves) (config : Config) : Prop where
  ensure : config.retag.ensureTreeExtra =
    GlobalAllocationMachine.ensure .global (pointerSource p image leaves).globals
  globalConstruction : (pointerSource p image leaves).globals =
    EvalGlobalAllocationMachine.make p image
      (EvalCoreMachine.extras leaves.sync ConcurrencyErrors.storeBuffer) (globalLeaves p image leaves)
  evaluate : (pointerSource p image leaves).globals.evaluateStaticInitializer =
    fun memory state definition =>
      let result := image.evaluateStaticInitializer {state with machine := {state.machine with memory}} definition
      ⟨result.state.machine.memory,result.state,result.outcome⟩
  beforeAccess : (pointerSource p image leaves).globals.beforeAccessGlobal =
    fun memory state _ _ _ _ => ⟨memory,state,.ok ()⟩

theorem make_global_fields (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : RootLeaves) (remaining : Nat) (contract : Construction p) :
    ∃ config : Config,
      EvalConfigurationCore.make p image bytes options leaves () (remaining+1) = .ok config ∧
      GlobalFields p image leaves config := by
  rw [EvalConfigurationCore.make_eq_context, EvalConfigurationCore.makeWithForeignContext]
  simp (config := {zeta := false}) only [contract.maximum_eq,
    EvalConfigurationCore.pureQuery_eq, EvalConfigurationCore.liftConstruction_eq,
    EvalMathMachine.hooks, CompilerCallConstruction.helpers,
    contract.i32_eq, contract.bool_eq, contract.u8_eq, contract.unit_eq, contract.rootSpan_eq,
    Except.mapError, Except.map, bind, Except.bind, pure, Except.pure]
  refine ⟨_, rfl, ?_⟩
  constructor
  all_goals with_unfolding_all rfl

theorem global_fields_of_make (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : RootLeaves) (remaining : Nat) (contract : Construction p) (config : Config)
    (built : EvalConfigurationCore.make p image bytes options leaves () (remaining+1) = .ok config) :
    GlobalFields p image leaves config := by
  obtain ⟨actual, equal, fields⟩ := make_global_fields p image bytes options leaves remaining contract
  have same : actual = config := Except.ok.inj (equal.symm.trans built)
  simpa only [same] using fields

/-- Managed source profiles prepare original bytes without allocating native
backing. This follows from the host policy, independently of runtime memory. -/
theorem global_bytes_prepare (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (prepared : EvalPreparation.Prepared) (debug : Bool) (id : AllocId)
    (bytes : Array UInt8) (align : Align) :
    (globalLeaves p image (Configuration.leaves prepared debug)).bytes.prepare id bytes align =
      pure (bytes,none) := by
  funext machine
  simp [EvalPointerSource.bytes, Configuration.leaves,
    bind, EStateM.bind, pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get]

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.CanonicalDictionaries." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved canonical dictionary axiom {dependency} in {name}"

end EmptyFunction.CanonicalDictionaries
