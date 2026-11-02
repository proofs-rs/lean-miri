import duplicate_prefix.CanonicalCopy
import duplicate_prefix.RootCompilerFacts

/-! Field identities of the actual canonical configuration. Every equation
is derived from the source builder; no effectful operation is assumed safe. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace DuplicatePrefix.CanonicalConfigFacts
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory

abbrev RootConfig := ExecutionMachine.Config MiriMemoryKind Machine.RootUser Unit Unit ABI.ExternAbi Unit
abbrev RootState := MachineHooks.State MiriMemoryKind Machine.RootUser
abbrev RootStored := EvalCoreMachine.Stored Unit Unit Unit Unit Unit Unit Unit Unit Machine.MinimalHost
abbrev RootPointers := PointerMachine.Hooks MiriMemoryKind (ValidityMachine.Control RootStored)
abbrev RootVTable := VTableHooks Provenance RootState Unit (FnVal Unit) (FnAbi MIR.TyId)
abbrev RootRawVTable := VTableHooks Provenance RootState Unit CallInstance (FnAbi MIR.TyId)
abbrev RootExtras := MemoryExtras.Hooks MiriMemoryKind Machine.RootUser Unit
abbrev RootDiscriminant := DiscriminantHooks Provenance RootState Unit (RuntimePlace Provenance)

private def metadataQuery {A : Type} (value : Except String A) : MachineHooks.M MiriMemoryKind Machine.RootUser A :=
  match value with
  | .ok value => pure value
  | .error reason => throw (.unsupported reason)

def pointeeQuery (compiler : CompilerProviders.Prepared) (ty : MIR.TyId) :
    MachineHooks.M MiriMemoryKind Machine.RootUser LocalLayout := do
  let some pointee ← metadataQuery (CompilerFacts.builtinDeref compiler.lifecycle.calls.symbols.facts.context ty true)
    | throw (.invalidProgram "pointee layout requested for a non-pointer type")
  metadataQuery (CompilerFacts.layoutOf compiler.lifecycle.calls.symbols.facts.context pointee)

structure Fields (compiler : CompilerProviders.Prepared) (image : AllocationImage.Imported) (options : EvalConfigurationCore.Options) (leaves : Machine.RootLeaves) (nested : Except StepError RootConfig) (config : RootConfig) : Prop where
  retagConstruction : ∃ (pointers : RootPointers) (table : RootRawVTable)
      (globals : GlobalAllocationHooks Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
        (PlaceMachine.AccessState MiriMemoryKind (ValidityMachine.UserState RootStored))) (choice : Unit),
    config.retag = EvalRetagMachine.hooks compiler.lifecycle.calls.symbols.facts compiler.lifecycle.calls.runtime
      (CompilerRetagOptions.make compiler options.retag) config.access config.projection table pointers choice ∧
    pointers.arithmetic = ⟨compiler.runtime.target.pointerSize⟩ ∧
    config.access.resolvePointer = TypedMemoryProviders.resolvePointer pointers ∧
    pointers.ensureTreeExtra = GlobalAllocationMachine.ensure .global globals ∧
    globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}}
  retagTypeShape : config.retag.typeShape = fun ty state =>
    match CompilerFacts.retagTypeShape compiler.lifecycle.calls.symbols.facts.context ty with
    | .ok value => .ok value state
    | .error reason => .error (.unsupported reason) state
  retagLog : config.retag.logCreation = fun _ _ _ _ _ => pure ()
  retagPrecise : config.retag.preciseInteriorMut = pure options.retag.preciseInteriorMut
  retagImplicit : config.retag.implicitWrites = pure options.retag.implicitWrites
  projectionDynamic : ∃ (table : RootRawVTable) (maximum : Size),
    CompilerExecutionBounds.maximum compiler.runtime.target = .ok maximum ∧
    config.projection.dynamic = EvalPlaceConstruction.dynamic compiler
      {debugAssertions := options.place.debugAssertions, maxSizeOfVal := maximum,
       dynamicFuel := options.place.dynamicFuel, validation := options.place.validation} table
  lifecycleAfterPop : ∃ (unwind : Unwind.Hooks MiriMemoryKind Machine.RootUser Unit Unit),
    config.lifecycle.afterPop = fun choice frame unwinding =>
      Unwind.afterStackPop unwind choice frame.extra unwinding
  projectionLocalToOp : config.projection.place.localToOp =
    PlaceMachine.localToOp (ValidityMachine.compilerPolicy config.compiler)
  projectionDynamicFuel : config.projection.dynamicFuel = options.place.dynamicFuel
  accessConstruction : ∃ (maximum : Size)
      (globals : GlobalAllocationHooks Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
        (PlaceMachine.AccessState MiriMemoryKind Machine.RootUser))
      (pointers : RootPointers) (extras : RootExtras),
    config.access = EvalAccessMachine.make compiler image maximum options.place.dynamicFuel globals pointers extras ∧
    globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}}
  canonicalCopy : ∃ context : CanonicalCopy.Context Unit Unit Unit Unit Unit Unit Unit Unit Machine.MinimalHost,
    config.access = context.access ∧ config.arithmetic = context.pointers.arithmetic ∧
    config.atomics.checkPointerAlign = fun (_ : Unit) => AtomicMachine.checkAlignment context.pointers
  isRawPointer : config.isRawPointer = fun (_ : Unit) ty => do
    let node ← match (compiler.runtime.node ty).mapError toString with
      | .ok node => pure node
      | .error reason => throw (.unsupported reason)
    match node.shapeKind with
    | .unknown _ => throw (.unsupported "raw pointer compiler type kind unavailable")
    | kind => pure (kind == .rawPointer)
  accessRuntime : config.access.runtime = compiler.runtime.target
  pointeeLayout : config.pointeeLayout = fun (_ : Unit) ty => pointeeQuery compiler ty
  arithmetic : config.arithmetic = ⟨compiler.runtime.target.pointerSize⟩
  addresses : config.addresses = PointerMachine.User.addresses
  atomicPointerSource : ∃ pointers : RootPointers,
    config.arithmetic = pointers.arithmetic ∧
    config.access.resolvePointer = TypedMemoryProviders.resolvePointer pointers ∧
    config.atomics.checkPointerAlign = fun (_ : Unit) => AtomicMachine.checkAlignment pointers
  pointerSource : ∃ pointers : RootPointers,
    config.arithmetic = pointers.arithmetic ∧
    config.access.resolvePointer = TypedMemoryProviders.resolvePointer pointers
  validity : ∃ (pointers : RootPointers) (vtable : RootVTable) (discriminant : RootDiscriminant),
    config.validity = EvalValidityMachine.hooks compiler.lifecycle.calls.symbols.facts
      compiler.lifecycle.calls.runtime
      (CompilerValidityLeaves.make compiler image EvalProjectionMachine.arrays config.projection pointers)
      config.access config.allocation config.compiler config.projection vtable discriminant
      pointers config.retag options.limits.retag
  validitySources : ∃ (pointers : RootPointers) (vtable : RootVTable) (discriminant : RootDiscriminant)
      (globals : GlobalAllocationHooks Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
        (PlaceMachine.AccessState MiriMemoryKind (ValidityMachine.UserState RootStored))),
    config.validity = EvalValidityMachine.hooks compiler.lifecycle.calls.symbols.facts
      compiler.lifecycle.calls.runtime
      (CompilerValidityLeaves.make compiler image EvalProjectionMachine.arrays config.projection pointers)
      config.access config.allocation config.compiler config.projection vtable discriminant
      pointers config.retag options.limits.retag ∧
    pointers.arithmetic = ⟨compiler.runtime.target.pointerSize⟩ ∧
    config.access.resolvePointer = TypedMemoryProviders.resolvePointer pointers ∧
    pointers.ensureTreeExtra = GlobalAllocationMachine.ensure .global globals ∧
    globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}}
  validate : config.compiler.validate = fun choice place =>
    match nested with
    | .error error => throw error
    | .ok inner => ValidityMachine.validateRuntime inner.validity choice options.limits.validation place true
  copyCompatible : config.copy.compatible = CompilerCovariance.compatible compiler options.place.debugAssertions
  copyPadding : config.copy.hasPadding = CompilerCopy.hasPadding compiler.runtime options.place.debugAssertions
  terminators : config.terminators = EvalTerminatorMachine.genericHooks leaves.control
    (EvalTerminatorMachine.ioGc leaves.blockingSources)
  retainTouched : config.access.retainTouched = fun machine _ => machine
  frameCompiler : config.lifecycle.compiler =
    CompilerFrameMetadata.hooks compiler.lifecycle.frames options.userRelevantCrates
  preambleSpan : config.lifecycle.preambleSpan = CompilerLifecycle.preambleSpan compiler.lifecycle.lifecycle
  requiredConstants : config.lifecycle.requiredConstants = CompilerLifecycle.requiredConstants compiler.lifecycle.lifecycle
  freshLocalsIdentity : config.lifecycle.freshLocalsIdentity = fun machine =>
    let (supply, label) := (EvalConfiguration.identity.get machine.user).allocate
    ({machine with user := EvalConfiguration.identity.put machine.user supply}, label)
  storage : config.lifecycle.storage.veryTriviallySized =
    CompilerStorage.veryTriviallySized compiler.runtime
  placeConstruction : ∃ (placeOptions : EvalPlaceConstruction.Options) (pointers : RootPointers) (table : RootRawVTable),
    config.compiler = EvalPlaceConstruction.compiler compiler placeOptions config.access pointers table
      config.compiler.checkPlaceType config.compiler.validate ∧
    config.projection = EvalPlaceConstruction.projection compiler placeOptions config.access config.allocation config.compiler table ∧
    config.operands.dereference = PointerPlaceMachine.dereference config.access
      (CompilerExecutionProviders.pointerCompiler compiler.lifecycle.calls.symbols.facts)
      config.projection.dynamic table config.projection.dynamicFuel
  compilerLocalSpan : config.compiler.localSpan = CompilerFrameContext.localSpan compiler
  layout : config.compiler.layout = fun (_ : Unit) id =>
    CompilerFrameContext.computeLocalLayout compiler id
  debug : config.compiler.debugAssertions = options.place.debugAssertions
  discriminant : config.discriminant = CompilerScalarLeaves.discriminant compiler
    (fun (_ : Unit) => ValidityMachine.scalarMayBeNull)
  rvalueNormalize : config.rvalues.normalize = fun (_ : Unit) => CompilerFrameContext.normalizeCastTarget compiler
  scalar : config.scalar = CompilerScalarLeaves.scalar compiler
  operandsDeref : ∃ (vtable : RootRawVTable),
    config.operands.dereference = PointerPlaceMachine.dereference config.access
      (CompilerExecutionProviders.pointerCompiler compiler.lifecycle.calls.symbols.facts)
      config.projection.dynamic vtable config.projection.dynamicFuel
  placeType : config.compiler.checkPlaceType =
    CompilerPlaceTypes.place compiler options.place.debugAssertions
      (CompilerCovariance.hook compiler options.place.debugAssertions)
  projectionFrameIndex : config.projection.place.frameIndex = do
    match (← get).stack.frameIndex with
    | .ok index => pure index
    | .error error => throw (.stack error)
  projectionResolveLayout : config.projection.place.resolveLayout = config.compiler.layout
  projectionSetFrame : config.projection.place.setFrame = MachineHooks.setCurrentFrame
  projectionGetFrame : config.projection.place.getFrame = MachineHooks.currentFrame
  projectionWriteLocal : config.projection.place.writeLocalImmediate = fun (_ : Unit) =>
    placeWriteLocalImmediate MachineHooks.currentFrame MachineHooks.setCurrentFrame
      ValidityMachine.validationInProgress MachineHooks.afterLocalWrite config.compiler.debugAbiCheck
  projectionWriteMemory : config.projection.place.writeMemoryNoValidate =
    fun (_ : Unit) value place => do
      let activeAccess ← ValidityMachine.scopedAccess config.access
      let validate ← ValidityMachine.enforceValidity
      PlaceMachine.writeMemory activeAccess (fun _ => validate) value place
  projectionDebug : config.projection.place.debugAssertions = options.place.debugAssertions
  compilerValidationInProgress : config.compiler.validationInProgress = ValidityMachine.validationInProgress
  compilerEnforce : config.compiler.enforceValidity = fun (_ : Unit) _ => ValidityMachine.enforceValidity
  validationRecursive : config.validationRecursive = fun (_ : Unit) _ => ValidityMachine.enforceValidityRecursively
  validityGhost (A : Type) : config.validity.withGhostValidation (A := A) = ValidityMachine.withGhostValidation
  projectionEnforce : config.projection.place.enforceValidity = fun (_ : Unit) _ => ValidityMachine.enforceValidity
  projectionValidate : config.projection.place.validate = config.compiler.validate
  debugAbiNoChecks : options.place.debugAssertions = false →
    config.compiler.debugAbiCheck = fun _ _ => pure ()
  projectionPlaceType : config.projection.place.checkPlaceType =
    CompilerPlaceTypes.place compiler options.place.debugAssertions
      (CompilerCovariance.hook compiler options.place.debugAssertions)
  operandType : config.operands.checkPlaceType =
    CompilerPlaceTypes.operand compiler options.place.debugAssertions
      (CompilerCovariance.hook compiler options.place.debugAssertions)
  callsDispatchConstruction : ∃
      (foreign : Option (MachineHooks.M MiriMemoryKind Machine.RootUser
        (ForeignItems.Hooks Provenance RootState (RuntimePlace Provenance) (RuntimePlace Provenance)
          (Pointer (Option Provenance)) LoadedBody CallInstance)))
      (backend : CallDispatchMachine.Backend RootState) (dynSym : Unit → String),
    config.calls.dispatch = CompilerCallConstruction.dispatch compiler foreign backend dynSym
  dispatchLoadMir : config.calls.dispatch.loadMir = config.helpers.loadMir
  callsBackend : config.calls.dispatch.backend =
    ⟨fun state => do
      match ← EvalBackendMachine.handler state.machine with
      | .none => pure .none
      | .vclocks _ => pure .vclocks⟩
  callCompiler : config.calls.compiler = CompilerCallConstruction.compiler compiler options.compatibilityBudget
  constantAt : options.place.debugAssertions = false → ∃ externStatic : MIR.DefId → MachineHooks.M MiriMemoryKind Machine.RootUser (Pointer Provenance),
    config.operands.constantAt = fun (_ : Unit) path constant known => do
      let site ← CompilerOperandSites.current path
      CompilerConstantMachine.evalAtBound compiler.constantBinding site config.functions config.arithmetic
        externStatic MemoryErrors.constant constant known
        none
  castTypeInfo : config.casts.typeInfo = fun (_ : Unit) ty state =>
    match CompilerFactAdapters.castTypeInfo compiler.lifecycle.calls.symbols.facts ty with
    | .ok value => .ok value state
    | .error reason => .error (.unsupported s!"cast compiler query: {reason}") state
  castLayout : config.casts.layoutOf = fun (_ : Unit) ty state =>
    match CompilerFacts.layoutOf compiler.lifecycle.calls.symbols.facts.context ty with
    | .ok value => .ok value state
    | .error reason => .error (.unsupported s!"cast compiler query: {reason}") state
  castDeref : config.casts.builtinDeref = fun (_ : Unit) ty explicit state =>
    match CompilerFacts.builtinDeref compiler.lifecycle.calls.symbols.facts.context ty explicit with
    | .ok value => .ok value state
    | .error reason => .error (.unsupported s!"cast compiler query: {reason}") state
  virtualCompiler : config.virtual.compiler = CompilerVirtualLeaves.make compiler.lifecycle.calls
  loadMir : config.helpers.loadMir = fun (_ : Unit) callee =>
    CompilerCallPipeline.loadMir compiler.lifecycle.calls callee

open Lean Meta Elab Tactic in
elab "supply_constant_extern" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let args := target.getAppArgs
  unless target.isAppOf ``Exists && args.size == 2 do throwError "expected extern-static witness"
  let predicate := args[1]!
  let body := predicate.bindingBody!
  let equality := body.getAppArgs
  let lhs ← whnf equality[1]!
  let rec find (expression : Expr) : Option Expr :=
    if expression.isAppOf ``CompilerConstantMachine.evalAtBound then
      let args := expression.getAppArgs
      if args.size ≥ 9 then some args[args.size - 5]! else none
    else match expression with
      | .app f a => (find f).orElse (fun _ => find a)
      | .lam _ t b _ | .forallE _ t b _ => (find t).orElse (fun _ => find b)
      | .letE _ t v b _ => (find t).orElse (fun _ => (find v).orElse (fun _ => find b))
      | .mdata _ b | .proj _ _ b => find b
      | _ => none
  let some witness := find lhs | throwError "actual constant adapter not found"
  if witness.hasLooseBVars then throwError "extern-static witness depends on operand binders"
  let witnessSyntax ← Term.exprToSyntax witness
  let mut debugName : Option Name := none
  for declaration in (← getLCtx) do
    debugName := some declaration.userName
  let some resolvedDebugName := debugName | throwError "missing no-debug option fact"
  let debugSyntax := mkIdent resolvedDebugName
  evalTactic (← `(tactic| refine ⟨$witnessSyntax, ?_⟩; simp only [$debugSyntax:ident]; with_unfolding_all rfl))

open Lean Meta Elab Tactic in
elab "supply_validity_constructor" : tactic => withMainContext do
  let target ← (← getMainGoal).getType
  let pointerPredicate := target.getAppArgs[1]!
  let vtablePredicate := pointerPredicate.bindingBody!.getAppArgs[1]!
  let discriminantPredicate := vtablePredicate.bindingBody!.getAppArgs[1]!
  let equality := discriminantPredicate.bindingBody!.getAppArgs
  let lhs ← instantiateMVars equality[1]!
  let rec find (expression : Expr) : Option Expr :=
    if expression.isAppOf ``EvalValidityMachine.hooks then some expression
    else match expression with
      | .app f a => (find f).orElse (fun _ => find a)
      | .lam _ t b _ | .forallE _ t b _ => (find t).orElse (fun _ => find b)
      | .letE _ t v b _ => (find t).orElse (fun _ => (find v).orElse (fun _ => find b))
      | .mdata _ b | .proj _ _ b => find b
      | _ => none
  let some source := find lhs | throwError "actual validity constructor not found"
  let arguments := source.getAppArgs
  unless arguments.size ≥ 12 do throwError "incomplete source validity constructor"
  let pointers := arguments[arguments.size - 3]!
  let vtable := arguments[arguments.size - 5]!
  let discriminant := arguments[arguments.size - 4]!
  if pointers.hasLooseBVars || vtable.hasLooseBVars || discriminant.hasLooseBVars then
    throwError "validity constructor witness depends on internal binders"
  let pointers ← Term.exprToSyntax pointers
  let vtable ← Term.exprToSyntax vtable
  let discriminant ← Term.exprToSyntax discriminant
  evalTactic (← `(tactic| refine ⟨$pointers, $vtable, $discriminant, ?_⟩; with_unfolding_all rfl))

open Lean Meta Elab Tactic in
elab "supply_validity_sources" : tactic => withMainContext do
  let target ← (← getMainGoal).getType
  let pointerPredicate := target.getAppArgs[1]!
  let vtablePredicate := pointerPredicate.bindingBody!.getAppArgs[1]!
  let discriminantPredicate := vtablePredicate.bindingBody!.getAppArgs[1]!
  let globalsPredicate := discriminantPredicate.bindingBody!.getAppArgs[1]!
  let equality := globalsPredicate.bindingBody!.getAppArgs[0]!.getAppArgs
  let lhs ← instantiateMVars equality[1]!
  let rec find (expression : Expr) : Option Expr :=
    if expression.isAppOf ``EvalValidityMachine.hooks then some expression
    else match expression with
      | .app f a => (find f).orElse (fun _ => find a)
      | .lam _ t b _ | .forallE _ t b _ => (find t).orElse (fun _ => find b)
      | .letE _ t v b _ => (find t).orElse (fun _ => (find v).orElse (fun _ => find b))
      | .mdata _ b | .proj _ _ b => find b
      | _ => none
  let some source := find lhs | throwError "actual validity constructor not found"
  let arguments := source.getAppArgs
  unless arguments.size ≥ 12 do throwError "incomplete source validity constructor"
  let pointers := arguments[arguments.size - 3]!
  let vtable := arguments[arguments.size - 5]!
  let discriminant := arguments[arguments.size - 4]!
  if pointers.hasLooseBVars || vtable.hasLooseBVars || discriminant.hasLooseBVars then
    throwError "validity constructor witness depends on internal binders"
  let globals ← mkAppM ``EvalPointerSource.Constructed.globals #[pointers.getAppArgs.back!]
  let globals ← Term.exprToSyntax globals
  let pointers ← Term.exprToSyntax pointers
  let vtable ← Term.exprToSyntax vtable
  let discriminant ← Term.exprToSyntax discriminant
  evalTactic (← `(tactic| refine ⟨$pointers, $vtable, $discriminant, $globals, rfl, ?_, ?_, ?_, ?_⟩))

open Lean Meta Elab Tactic in
elab "supply_dispatch_constructor" : tactic => withMainContext do
  let target ← (← getMainGoal).getType
  let p1 := target.getAppArgs[1]!
  let p2 := p1.bindingBody!.getAppArgs[1]!
  let p3 := p2.bindingBody!.getAppArgs[1]!
  let equality := p3.bindingBody!.getAppArgs
  let lhs ← instantiateMVars equality[1]!
  let rec find (expression : Expr) : Option Expr :=
    if expression.isAppOf ``CompilerCallConstruction.leaves then some expression
    else match expression with
      | .app f a => (find f).orElse (fun _ => find a)
      | .lam _ t b _ | .forallE _ t b _ => (find t).orElse (fun _ => find b)
      | .letE _ t v b _ => (find t).orElse (fun _ => (find v).orElse (fun _ => find b))
      | .mdata _ b | .proj _ _ b => find b
      | _ => none
  let some source := find lhs | throwError "actual call leaves constructor not found"
  let args := source.getAppArgs
  let foreign ← Term.exprToSyntax args[args.size - 4]!
  let backend ← Term.exprToSyntax args[args.size - 3]!
  let dynSym ← Term.exprToSyntax args[args.size - 2]!
  evalTactic (← `(tactic| refine ⟨$foreign, $backend, $dynSym, ?_⟩; with_unfolding_all rfl))

open Lean Meta Elab Tactic in
elab "supply_copy_context" : tactic => withMainContext do
  let target ← (← getMainGoal).getType
  let predicate := target.getAppArgs[1]!
  let equality := predicate.bindingBody!.getAppArgs[0]!.getAppArgs
  let lhs ← instantiateMVars equality[1]!
  let rec find (name : Name) (expression : Expr) : Option Expr :=
    if expression.isAppOf name then some expression
    else match expression with
      | .app f a => (find name f).orElse (fun _ => find name a)
      | .lam _ t b _ | .forallE _ t b _ => (find name t).orElse (fun _ => find name b)
      | .letE _ t v b _ => (find name t).orElse (fun _ => (find name v).orElse (fun _ => find name b))
      | .mdata _ b | .proj _ _ b => find name b
      | _ => none
  let some access := find ``EvalAccessMachine.make lhs | throwError "actual access constructor not found"
  let args := access.getAppArgs
  let pointers := args[args.size - 2]!
  let source := pointers.getAppArgs.back!
  let some expanded ← unfoldDefinition? source true | throwError "actual pointer source cannot be unfolded"
  let expanded ← zetaReduce expanded
  let some globals := find ``EvalGlobalAllocationMachine.make expanded | throwError "actual global constructor absent"
  let globalLeaves := globals.getAppArgs.back!
  let extras := args[args.size - 1]!
  let extraArgs := extras.getAppArgs
  let context ← mkAppM ``CanonicalCopy.Context.mk #[args[args.size - 7]!, args[args.size - 6]!,
    args[args.size - 5]!, args[args.size - 4]!, globalLeaves, pointers,
    extraArgs[extraArgs.size - 2]!, extraArgs.back!]
  if context.hasLooseBVars then throwError "copy context contains local binder indices"
  let context ← Term.exprToSyntax context
  evalTactic (← `(tactic| refine ⟨$context, ?_, ?_, ?_⟩))

open Lean Meta Elab Tactic in
elab "supply_access_constructor" : tactic => withMainContext do
  let target ← (← getMainGoal).getType
  let p1 := target.getAppArgs[1]!
  let p2 := p1.bindingBody!.getAppArgs[1]!
  let p3 := p2.bindingBody!.getAppArgs[1]!
  let p4 := p3.bindingBody!.getAppArgs[1]!
  let equality := p4.bindingBody!.getAppArgs[0]!.getAppArgs
  let lhs ← instantiateMVars equality[1]!
  let rec find (expression : Expr) : Option Expr :=
    if expression.isAppOf ``EvalAccessMachine.make then some expression
    else match expression with
      | .app f a => (find f).orElse (fun _ => find a)
      | .lam _ t b _ | .forallE _ t b _ => (find t).orElse (fun _ => find b)
      | .letE _ t v b _ => (find t).orElse (fun _ => (find v).orElse (fun _ => find b))
      | .mdata _ b | .proj _ _ b => find b
      | _ => none
  let some source := find lhs | throwError "actual access constructor not found"
  let arguments := source.getAppArgs
  let maximum ← Term.exprToSyntax arguments[arguments.size - 5]!
  let globals ← Term.exprToSyntax arguments[arguments.size - 3]!
  let pointers ← Term.exprToSyntax arguments[arguments.size - 2]!
  let extras ← Term.exprToSyntax arguments[arguments.size - 1]!
  evalTactic (← `(tactic| refine ⟨$maximum, $globals, $pointers, $extras, ?_, ?_⟩))

open Lean Meta Elab Tactic in
elab "supply_retag_constructor" : tactic => withMainContext do
  let target ← (← getMainGoal).getType
  let p1 := target.getAppArgs[1]!
  let p2 := p1.bindingBody!.getAppArgs[1]!
  let p3 := p2.bindingBody!.getAppArgs[1]!
  let p4 := p3.bindingBody!.getAppArgs[1]!
  let equality := p4.bindingBody!.getAppArgs[0]!.getAppArgs
  let lhs ← instantiateMVars equality[1]!
  let rec find (expression : Expr) : Option Expr :=
    if expression.isAppOf ``EvalRetagMachine.hooks then some expression
    else match expression with
      | .app f a => (find f).orElse (fun _ => find a)
      | .lam _ t b _ | .forallE _ t b _ => (find t).orElse (fun _ => find b)
      | .letE _ t v b _ => (find t).orElse (fun _ => (find v).orElse (fun _ => find b))
      | .mdata _ b | .proj _ _ b => find b
      | _ => none
  let some source := find lhs | throwError "actual retag constructor not found"
  let arguments := source.getAppArgs
  let pointers := arguments[arguments.size - 2]!
  let globals ← mkAppM ``EvalPointerSource.Constructed.globals #[pointers.getAppArgs.back!]
  let globals ← Term.exprToSyntax globals
  let pointers ← Term.exprToSyntax pointers
  let table ← Term.exprToSyntax arguments[arguments.size - 3]!
  let choice ← Term.exprToSyntax arguments.back!
  evalTactic (← `(tactic| refine ⟨$pointers, $table, $globals, $choice, rfl, ?_, ?_, ?_, ?_⟩))

open Lean Meta Elab Tactic in
elab "supply_place_constructor" : tactic => withMainContext do
  let target ← (← getMainGoal).getType
  let optionsPredicate := target.getAppArgs[1]!
  let pointerPredicate := optionsPredicate.bindingBody!.getAppArgs[1]!
  let tablePredicate := pointerPredicate.bindingBody!.getAppArgs[1]!
  let equality := tablePredicate.bindingBody!.getAppArgs[0]!.getAppArgs
  let lhs ← instantiateMVars equality[1]!
  let rec find (expression : Expr) : Option Expr :=
    if expression.isAppOf ``EvalPlaceConstruction.compiler then some expression
    else match expression with
      | .app f a => (find f).orElse (fun _ => find a)
      | .lam _ t b _ | .forallE _ t b _ => (find t).orElse (fun _ => find b)
      | .letE _ t v b _ => (find t).orElse (fun _ => (find v).orElse (fun _ => find b))
      | .mdata _ b | .proj _ _ b => find b
      | _ => none
  let some source := find lhs | throwError "actual place compiler constructor not found"
  let arguments := source.getAppArgs
  let options ← Term.exprToSyntax arguments[arguments.size - 6]!
  let pointers ← Term.exprToSyntax arguments[arguments.size - 4]!
  let table ← Term.exprToSyntax arguments[arguments.size - 3]!
  evalTactic (← `(tactic| refine ⟨$options, $pointers, $table, ?_, ?_, ?_⟩ <;> with_unfolding_all rfl))

open Lean Meta Elab Tactic in
elab "supply_source_pointers" : tactic => withMainContext do
  let target ← (← getMainGoal).getType
  let predicate := target.getAppArgs[1]!
  let conjunction := predicate.bindingBody!.getAppArgs
  let equality := conjunction[0]!.getAppArgs
  let lhs ← instantiateMVars equality[1]!
  let rec find (expression : Expr) : Option Expr :=
    if expression.isAppOf ``EvalValidityMachine.hooks then
      let arguments := expression.getAppArgs
      if arguments.size ≥ 12 then some arguments[arguments.size - 3]! else none
    else match expression with
      | .app f a => (find f).orElse (fun _ => find a)
      | .lam _ t b _ | .forallE _ t b _ => (find t).orElse (fun _ => find b)
      | .letE _ t v b _ => (find t).orElse (fun _ => (find v).orElse (fun _ => find b))
      | .mdata _ b | .proj _ _ b => find b
      | _ => none
  let some source := find lhs | throwError "actual source pointer constructor not found"
  if source.hasLooseBVars then throwError "pointer constructor depends on internal binders"
  let source ← Term.exprToSyntax source
  evalTactic (← `(tactic| refine ⟨$source, ?_, ?_⟩))

private theorem make_with_fields (p : CompilerProviders.Prepared)
    (image : AllocationImage.Imported) (bytes : CompilerGlobalBytes.Prepared)
    (options : EvalConfigurationCore.Options) (leaves : Machine.RootLeaves)
    (choice : Unit) (remaining : Nat) (contract : PreparedContracts.CompilerConstruction p) :
    ∃ config, EvalConfigurationCore.make p image bytes options leaves choice (remaining + 1) = .ok config ∧
      Fields p image options leaves
        (EvalConfigurationCore.make p image bytes options leaves choice remaining) config := by
  unfold EvalConfigurationCore.make
  unfold_factory_helpers
  rw [EvalConfigurationCore.makeWithForeignContext]
  simp (config := {zeta := false}) only [contract.maximum_eq]
  unfold_factory_helpers
  simp (config := {zeta := false}) only [EvalMathMachine.hooks,
    CompilerCallConstruction.helpers, contract.i32_eq, contract.bool_eq,
    contract.u8_eq, contract.unit_eq, contract.rootSpan_eq,
    Except.mapError, Except.map, bind, Except.bind, pure, Except.pure]
  refine ⟨_, rfl, ?_⟩
  constructor
  all_goals try with_unfolding_all rfl
  case retagConstruction =>
    supply_retag_constructor
    · with_unfolding_all rfl
    · simp only [Option.map_none, Option.map_some, EvalAccessMachine.make,
          EvalBackendMachine.access] <;> rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
  case placeConstruction =>
    supply_place_constructor
  case lifecycleAfterPop =>
    with_unfolding_all exact ⟨_, rfl⟩
  case projectionDynamic =>
    with_unfolding_all exact ⟨_, contract.maximum, contract.maximum_eq, rfl⟩
  case operandsDeref =>
    with_unfolding_all exact ⟨_, rfl⟩
  case callsDispatchConstruction =>
    supply_dispatch_constructor
  case callsBackend =>
    simp only [CompilerCallConstruction.leaves, CompilerCallConstruction.dispatch]
    apply congrArg CallDispatchMachine.Backend.mk
    funext state
    cases result : EvalBackendMachine.handler state.machine with
    | error reason => with_unfolding_all simp only [result, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
    | ok handler => cases handler <;> with_unfolding_all simp only [result, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  case canonicalCopy =>
    supply_copy_context
    · dsimp only
      with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
  case isRawPointer =>
    unfold_factory_helpers
    funext c ty state
    unfold_internal ".EvalConfigurationCore.query"
    cases query : p.runtime.node ty <;> simp [query, Except.mapError, bind, EStateM.bind, pure, EStateM.pure] <;> with_unfolding_all rfl
  case accessConstruction =>
    supply_access_constructor
    · with_unfolding_all rfl
    · with_unfolding_all rfl
  case atomicPointerSource =>
    supply_source_pointers
    · with_unfolding_all rfl
    · constructor
      · simp only [Option.map_none, Option.map_some, EvalAccessMachine.make,
            EvalBackendMachine.access] <;> rfl
      · with_unfolding_all rfl
  case pointerSource =>
    supply_source_pointers
    · with_unfolding_all rfl
    · simp only [Option.map_none, Option.map_some, EvalAccessMachine.make,
          EvalBackendMachine.access] <;> rfl
  case validitySources =>
    supply_validity_sources
    · with_unfolding_all rfl
    · simp only [Option.map_none, Option.map_some, EvalAccessMachine.make,
          EvalBackendMachine.access] <;> rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
  case validity =>
    supply_validity_constructor
  case validate =>
    unfold_factory_helpers
    dsimp only [EvalPlaceConstruction.compiler]
    funext c place
    cases h : EvalConfigurationCore.makeWithForeignContext (Assembly := Unit)
      p image bytes options leaves choice none none remaining <;> rfl
  case validityGhost =>
    intro A
    rfl
  case debugAbiNoChecks =>
    intro debugFalse
    dsimp only [EvalPlaceConstruction.compiler]
    simp only [debugFalse, Bool.false_eq_true, ite_false]
  case constantAt =>
    intro debugFalse
    supply_constant_extern
  case retagTypeShape =>
    dsimp only [EvalRetagMachine.hooks]
    funext ty state
    cases h : CompilerFacts.retagTypeShape p.lifecycle.calls.symbols.facts.context ty <;> rfl
  case castTypeInfo =>
    dsimp only [CompilerCastLeaves.make]
    funext c ty state
    cases h : CompilerFactAdapters.castTypeInfo p.lifecycle.calls.symbols.facts ty <;> rfl
  case castLayout =>
    dsimp only [CompilerCastLeaves.make]
    funext c ty state
    cases h : CompilerFacts.layoutOf p.lifecycle.calls.symbols.facts.context ty <;> rfl
  case castDeref =>
    dsimp only [CompilerCastLeaves.make]
    funext c ty explicit state
    cases h : CompilerFacts.builtinDeref p.lifecycle.calls.symbols.facts.context ty explicit <;> rfl

theorem actual_fields (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    Fields PreparedReflection.actual.compiler PreparedReflection.actual.image options
      (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions)
      (Machine.actualConfig options choice remaining)
      (PreparedContracts.actualConfig options choice remaining span) := by
  obtain ⟨config, construction, fields⟩ := make_with_fields PreparedReflection.actual.compiler
    PreparedReflection.actual.image PreparedReflection.actual.bytes options
    (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions)
    choice remaining (PreparedContracts.actualConstruction span)
  have eq := PreparedContracts.actualConfig_eq options choice remaining span
  change EvalConfigurationCore.make PreparedReflection.actual.compiler PreparedReflection.actual.image
    PreparedReflection.actual.bytes options
    (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions)
    choice (remaining + 1) = .ok _ at eq
  rw [construction] at eq
  have same : config = PreparedContracts.actualConfig options choice remaining span := Except.ok.inj eq
  exact same ▸ fields

theorem actual_storage_bool (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    (PreparedContracts.actualConfig options choice remaining span).lifecycle.storage.veryTriviallySized 0 =
      .ok true := by
  rw [(actual_fields options choice remaining span).storage]
  exact RootCompilerFacts.root_storage_trivial_bool

theorem actual_storage_slice (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    (PreparedContracts.actualConfig options choice remaining span).lifecycle.storage.veryTriviallySized 3 =
      .ok true := by
  rw [(actual_fields options choice remaining span).storage]
  exact RootCompilerFacts.root_storage_trivial_slice

theorem actual_storage_type2 (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    (PreparedContracts.actualConfig options choice remaining span).lifecycle.storage.veryTriviallySized 2 =
      .ok true := by
  rw [(actual_fields options choice remaining span).storage]
  exact RootCompilerFacts.root_storage_trivial_type2

theorem actual_storage_usize (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    (PreparedContracts.actualConfig options choice remaining span).lifecycle.storage.veryTriviallySized 5 =
      .ok true := by
  rw [(actual_fields options choice remaining span).storage]
  exact RootCompilerFacts.root_storage_trivial_usize

theorem actual_term_get_set (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (control : TerminatorMachine.Control Unit) (user : Machine.RootUser) :
    let config := PreparedContracts.actualConfig options choice remaining span
    config.terminators.getControl (config.terminators.setControl control user) = control := by
  dsimp only
  rw [(actual_fields options choice remaining span).terminators]
  rfl

theorem actual_term_set_set (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (first second : TerminatorMachine.Control Unit) (user : Machine.RootUser) :
    let config := PreparedContracts.actualConfig options choice remaining span
    config.terminators.setControl second (config.terminators.setControl first user) =
      config.terminators.setControl second user := by
  dsimp only
  rw [(actual_fields options choice remaining span).terminators]
  rfl

theorem with_validation_validate (config : RootConfig) (limits : ExecutionMachine.Limits) :
    (ExecutionMachine.withValidation config limits).compiler.validate = (fun choice place => do
      let recursiveValidation ← config.validationRecursive choice place.layout
      ValidityVisitor.validatePlace
        (TypedMachineBindings.bindValidity config.validity config.retag limits.retag)
        choice limits.validation place recursiveValidation true) := by rfl

theorem actual_validate_successor (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    (PreparedContracts.actualConfig options choice (remaining + 1) span).compiler.validate =
      (fun c place => ValidityMachine.validateRuntime
        (PreparedContracts.actualConfig options choice remaining span).validity
        c options.limits.validation place true) := by
  have field := (actual_fields options choice (remaining + 1) span).validate
  rw [PreparedContracts.actualConfig_eq options choice remaining span] at field
  exact field

theorem pointee_query_supported (compiler : CompilerProviders.Prepared)
    (pointerTy pointeeTy : MIR.TyId) (layout : LocalLayout)
    (deref : CompilerFacts.builtinDeref compiler.lifecycle.calls.symbols.facts.context pointerTy true = .ok (some pointeeTy))
    (lookup : CompilerFacts.layoutOf compiler.lifecycle.calls.symbols.facts.context pointeeTy = .ok layout) :
    pointeeQuery compiler pointerTy = pure layout := by
  funext state
  unfold pointeeQuery
  rw [deref]
  simp only [metadataQuery, bind, EStateM.bind, pure, EStateM.pure]
  rw [lookup]
  rfl

theorem actual_arithmetic (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    (PreparedContracts.actualConfig options choice remaining span).arithmetic = ⟨Size.ofBytes 8⟩ := by
  rw [(actual_fields options choice remaining span).arithmetic]
  rfl

theorem actual_access_runtime (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    (PreparedContracts.actualConfig options choice remaining span).access.runtime =
      PreparedReflection.actual.runtime.target :=
  (actual_fields options choice remaining span).accessRuntime

theorem actual_target_width (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    (PreparedContracts.actualConfig options choice remaining span).access.runtime.base.pointerWidth = .w64 := by
  rw [actual_access_runtime]
  rfl

theorem actual_retain_touched (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    (PreparedContracts.actualConfig options choice remaining span).access.retainTouched =
      fun machine _ => machine :=
  (actual_fields options choice remaining span).retainTouched

open Lean Elab Command in
run_cmd do
  for declaration in #[``actual_fields, ``actual_storage_bool,
      ``actual_storage_type2, ``actual_storage_usize, ``actual_storage_slice, ``actual_term_get_set, ``actual_term_set_set,
      ``actual_retain_touched, ``with_validation_validate, ``actual_validate_successor,
      ``actual_arithmetic, ``actual_access_runtime, ``actual_target_width, ``pointee_query_supported] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"

end DuplicatePrefix.CanonicalConfigFacts
