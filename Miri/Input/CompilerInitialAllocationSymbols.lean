import Miri.Input.CompilerInitialAllocationSnapshot
import Miri.Input.GenericInstantiationWorld
import Miri.Input.TypeArenaPredicateWorld

/-! Raw snapshot symbols enter the same execution-owned type universe as MIR.
This adapter performs construction in a candidate World. It never treats raw
compiler source IDs or exporter graph IDs as runtime type/definition identities.
Unsupported structural forms remain errors from the actual World constructors. -/
namespace Miri.Input.CompilerInitialAllocation.RawSymbols
open Lean GenericSubstitution TypeArena Miri.Interpreter
set_option autoImplicit false
private def lift {α : Type} (result : Except String α) : WorldM α :=
  match result with | .ok value => pure value | .error error => throw error
private def field (j : Json) (name : String) : WorldM Json := lift (j.getObjVal? name)
private def text (j : Json) (name : String) : WorldM String := do lift ((← field j name).getStr?)
private def flag (j : Json) (name : String) : WorldM Bool := do lift ((← field j name).getBool?)
def type (j : Json) : WorldM TypeId := do
  let term ← lift (GenericMaterialCodec.readTerm 1024 j)
  GenericInstantiationWorld.resolveType 16384 term
private def definition (j : Json) (name : String := "definition") : WorldM Miri.MIR.DefId := do
  let identity ← lift (GenericMaterialCodec.readDefinition (← field j name))
  let world ← get
  lift (world.definitionRef identity)
private def childType (j : Json) (name : String) : WorldM TypeId := do type (← field j name)
def instanceKind (j : Json) : WorldM CallInstanceKind := do
  match ← text j "kind" with
  | "item" => return .Item (← definition j)
  | "intrinsic" => return .Intrinsic (← definition j)
  | "llvm_intrinsic" => return .LlvmIntrinsic (← definition j)
  | "virtual" => return .Virtual (← definition j) (← lift ((← field j "dispatch_slot").getNat?))
  | "shim" =>
    let shim ← field j "shim"
    let kind ← text shim "kind"
    let value : CallShimKind ← do
      match kind with
        | "vtable" => pure (CallShimKind.VTable (← definition shim))
        | "reify" => do
          let raw ← field shim "reason"
          let reason ← if raw == .null then pure none else do
            match ← lift raw.getStr? with
            | "function_pointer" => pure ((some CallReifyReason.FnPtr))
            | "vtable" => pure ((some CallReifyReason.Vtable))
            | _ => throw "unknown raw reify reason"
          pure (.Reify (← definition shim) reason)
        | "function_pointer" => pure (.FnPtr (← definition shim) (← childType shim "function_type"))
        | "closure_once" => pure (.ClosureOnce (← definition shim "call_once_definition") (← definition shim "closure_definition") (← flag shim "track_caller"))
        | "construct_coroutine_in_closure" => pure (.ConstructCoroutineInClosure (← definition shim) (← flag shim "receiver_by_ref"))
        | "thread_local" => pure (.ThreadLocal (← definition shim))
        | "future_drop_poll" => pure (.FutureDropPoll (← definition shim) (← childType shim "proxy_type") (← childType shim "implementation_type"))
        | "drop_glue" => do
          let raw ← field shim "drop_type"
          pure (.DropGlue (← definition shim) (← if raw == .null then pure none else some <$> type raw))
        | "clone" => pure (.Clone (← definition shim) (← childType shim "clone_type"))
        | "function_pointer_as_pointer" => pure (.FnPtrAsPtr (← definition shim) (← childType shim "function_type"))
        | "function_pointer_from_pointer" => pure (.FnPtrFromPtr (← definition shim) (← childType shim "function_type"))
        | "async_drop_glue_constructor" => pure (.AsyncDropGlueCtor (← definition shim) (← childType shim "drop_type"))
        | "async_drop_glue" => pure (.AsyncDropGlue (← definition shim) (← childType shim "coroutine_type"))
        | _ => throw "unknown raw shim kind"
    pure (.Shim value)
  | _ => throw "unknown raw instance kind"
def decodeInstance (j : Json) : WorldM InstanceArena.Key := do
  let kind ← instanceKind (← field j "kind")
  let raw ← lift ((← field j "arguments").getArr?)
  let terms ← lift (raw.mapM (GenericMaterialCodec.readTerm 1024))
  let args ← GenericInstantiationWorld.resolveArguments 16384 terms
  let world ← get
  lift (InstanceArena.Key.ofSource world kind args)
private def boundVariable (value : BoundVariable) : WorldM Miri.MIR.BoundVariableKind := do
  let world ← get
  match value with
  | .constant => pure .Const
  | .type .anonymous => pure (.Type .Anon)
  | .type (.named definition) => return .Type (.Param (← lift (world.definitionRef definition)))
  | .type _ => throw "raw bound type identity not representable by compiler MIR kind"
  | .region .anonymous => pure (.Region .Anon)
  | .region (.named definition) => return .Region (.Named (← lift (world.definitionRef definition)))
  | .region (.namedForPrinting name) => pure (.Region (.NamedForPrinting name))
  | .region .closureEnvironment => pure (.Region .ClosureEnv)
private def argument (term : GenericSubstitution.Term) : WorldM Miri.MIR.GenericArg := do
  let arguments ← GenericInstantiationWorld.resolveArguments 16384 #[term]
  let some value := arguments[0]? | throw "predicate argument construction returned no value"
  pure value
def predicates (raw : Json) : WorldM (Array VtablePredicate) := do
  let rows ← lift raw.getArr?
  rows.mapM fun row => do
    let term ← lift (GenericMaterialCodec.readTerm 1024 row)
    let predicate ← DynamicPredicate.read argument term
    let _ ← World.internExistential predicate
    let world ← get
    let definition ← lift (world.definitionRef predicate.body.definition)
    let variables ← predicate.variables.mapM boundVariable
    let kind := match predicate.body with
      | .trait .. => VtablePredicateKind.trait
      | .autoTrait .. => VtablePredicateKind.autoTrait
      | .projection .. => VtablePredicateKind.projection
    let projection := match predicate.body with
      | .projection _ _ (.type id) => some (PredicateProjectionTerm.type id)
      | .projection _ _ (.constant id) => some (PredicateProjectionTerm.constant id)
      | _ => none
    pure {kind := kind, definitionId := definition, definitionPath := none, genericArgs := predicate.body.arguments, boundVariables := variables, projectionTerm := projection}
end Miri.Input.CompilerInitialAllocation.RawSymbols
