import duplicate_prefix.Prepared
import duplicate_prefix.Machine
import Miri.Input.CompilerCallConstruction
import Lean

/-! Explicit, effect-free compiler-query contracts. These are metadata
coherence/support obligations, never assumptions that a memory access, call
step, or Rust execution is safe. The opaque source Json comparator is not
replaced or assigned an unchecked axiom. -/

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace DuplicatePrefix.PreparedContracts
open Lean Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory

/-- All fields concern immutable compiler data. In particular this contract
mentions no runtime state, pointer permission, memory access or step outcome. -/
structure CompilerConstruction (compiler : CompilerProviders.Prepared) where
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

/-- The only unknown in this contract is the existing opaque Json BEq's
self-comparison on this exact fixed source. It is an external metadata
comparator contract, not an assertion about the interpreter's safety. -/
structure SourceComparator where
  reflexive : (PreparedReflection.actual.runtime.source.raw ==
    PreparedReflection.actual.runtime.source.raw) = true

theorem fixed_source_matches (contract : SourceComparator)
    (certificate : Option (RuntimeMetadata.JsonReflexivity PreparedReflection.actual.runtime.source.raw)) :
    RuntimeMetadata.JsonReflexivity.matchesRightOr certificate
      PreparedReflection.actual.compiler.program.input.raw = true := by
  rw [RuntimeMetadata.JsonReflexivity.matchesRightOr_eq]
  exact contract.reflexive

open Lean Elab Tactic in
elab "unfold_factory_helpers" : tactic => do
  let env ← getEnv
  let suffixes := [".EvalConfigurationCore.makeWithForeign", ".EvalConfigurationCore.pureQuery",
    ".EvalConfigurationCore.liftConstruction"]
  let names ← suffixes.mapM fun (suffix : String) => do
    let candidates := env.constants.toList.filterMap fun (name, _) =>
      if name.toString.endsWith suffix then some name else none
    match candidates with
    | [name] => pure (mkIdent name)
    | _ => throwError "expected one source helper {suffix}, found {candidates.length}"
  let names := names.toArray
  evalTactic (← `(tactic| simp (config := {zeta := false}) only [$[$names:ident],*]))

set_option autoImplicit false in
theorem canonical_make_success
    {Os R Payload H D Other Aff B Host Choice ClockHost : Type}
    (compiler : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : EvalConfigurationCore.Leaves Os R Payload H D Other Aff B Host Choice ClockHost)
    (choice : Choice) (remaining : Nat) (contract : CompilerConstruction compiler) :
    ∃ config, EvalConfigurationCore.make compiler image bytes options leaves choice (remaining + 1) = .ok config := by
  unfold EvalConfigurationCore.make
  unfold_factory_helpers
  rw [EvalConfigurationCore.makeWithForeignContext]
  simp (config := {zeta := false}) only [contract.maximum_eq]
  unfold_factory_helpers
  simp (config := {zeta := false}) only [EvalMathMachine.hooks,
    CompilerCallConstruction.helpers, contract.i32_eq, contract.bool_eq,
    contract.u8_eq, contract.unit_eq, contract.rootSpan_eq,
    Except.mapError, Except.map, bind, Except.bind, pure, Except.pure]
  exact ⟨_, rfl⟩



/-- Link the prepared interpreter program to the separately reflected root
MIR body by a kernel reduction over the fixed data. -/
theorem fixed_root_body :
    (PreparedReflection.actual.program.bundle.bodies[RootBody.reflected.body.identity.index]?).map LoweredBody.body =
      some RootBody.reflected.body.body := by rfl

/-- The real canonical instance-body lookup resolves the reflected root with
its exact body identity and all source instantiation checks. -/
theorem fixed_root_loaded :
    CallResolution.loadedBodyOfInstance PreparedReflection.actual.compiler.lifecycle.calls.calls
      RootBody.reflected.functionInstance = .ok RootBody.reflected.body := by rfl

/-- The single construction-time metadata assumption left opaque by the
existing partial compiler-value decoder. It concerns the fixed dummy-span
query only, not a runtime memory or execution operation. -/
structure FixedSpanQuery where
  rootSpan_eq : CompilerContextSpan.rootSpan PreparedReflection.actual.program =
    .ok PreparedReflection.actual.dummySpan

private def checkedOk {Error Value : Type} :
    (value : Except Error Value) → value.isOk = true → Value
  | .ok value, _ => value
  | .error _, impossible => False.elim (by cases impossible)

private theorem checkedOk_eq {Error Value : Type}
    (value : Except Error Value) (success : value.isOk = true) :
    value = .ok (checkedOk value success) := by
  cases value with
  | ok value => rfl
  | error _ => cases success

theorem maximum_supported :
    (CompilerExecutionBounds.maximum PreparedReflection.actual.runtime.target).isOk = true := by rfl

theorem i32_supported :
    (PreparedReflection.actual.compiler.primitiveLayout "i32").isOk = true := by rfl

theorem bool_supported :
    (PreparedReflection.actual.compiler.primitiveLayout "bool").isOk = true := by rfl

theorem u8_supported :
    (PreparedReflection.actual.compiler.primitiveLayout "u8").isOk = true := by rfl

theorem unit_supported :
    (PreparedReflection.actual.compiler.primitiveLayout "unit").isOk = true := by rfl

/-- Five construction queries are kernel-computed on the fixed metadata;
only the existing opaque dummy-span decode needs an explicit contract. -/
def actualConstruction (span : FixedSpanQuery) :
    CompilerConstruction PreparedReflection.actual.compiler where
  maximum := checkedOk _ maximum_supported
  maximum_eq := checkedOk_eq _ maximum_supported
  i32 := checkedOk _ i32_supported
  i32_eq := checkedOk_eq _ i32_supported
  bool := checkedOk _ bool_supported
  bool_eq := checkedOk_eq _ bool_supported
  u8 := checkedOk _ u8_supported
  u8_eq := checkedOk_eq _ u8_supported
  unit := checkedOk _ unit_supported
  unit_eq := checkedOk_eq _ unit_supported
  rootSpan := PreparedReflection.actual.dummySpan
  rootSpan_eq := span.rootSpan_eq

theorem actual_config_success (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : FixedSpanQuery) :
    ∃ config, Machine.actualConfig options choice (remaining + 1) = .ok config := by
  unfold Machine.actualConfig Machine.rootConfig
  exact canonical_make_success _ _ _ _ _ _ _ (actualConstruction span)

/-- The actual configuration selected from the proved successful canonical
builder. This definition carries the metadata-span contract explicitly. -/
noncomputable def actualConfig (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : FixedSpanQuery) :=
  Classical.choose (actual_config_success options choice remaining span)

theorem actualConfig_eq (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : FixedSpanQuery) :
    Machine.actualConfig options choice (remaining + 1) =
      .ok (actualConfig options choice remaining span) :=
  Classical.choose_spec (actual_config_success options choice remaining span)

open Lean Elab Command in
run_cmd do
  for declaration in #[``fixed_source_matches, ``canonical_make_success, ``fixed_root_body, ``fixed_root_loaded,
      ``maximum_supported, ``i32_supported, ``bool_supported, ``u8_supported,
      ``unit_supported, ``actualConstruction, ``actual_config_success, ``actualConfig_eq] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"

end DuplicatePrefix.PreparedContracts
