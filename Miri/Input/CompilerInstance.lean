import Miri.Input.CompilerGlobals
import Miri.Interpreter.Instance

/-! Exact instance_kind_json schema mirrors pinned ty/instance.rs. No shim or
generic argument is collapsed to its definition ID. -/
namespace Miri.Input.CompilerInstance
open Lean Miri.Interpreter
private abbrev M := StateT CompilerTables (Except String)
private def field (j : Json) (key : String) : Except String Json := j.getObjVal? key
private def str (j : Json) (key : String) : Except String String := do (← field j key).getStr?
private def boolean (j : Json) (key : String) : Except String Bool := do (← field j key).getBool?
private def natural (j : Json) (key : String) : Except String Nat := do (← field j key).getNat?
private def definition (j : Json) (key : String) : M MIR.DefId := do
  let j ← field j key
  let id : DefinitionId := ⟨← natural j "crate", ← natural j "index"⟩
  let state ← get
  match lookupDefinitionId state.definitions id with
  | .ok id => pure id
  | .error _ =>
    set { state with definitions := state.definitions.push id }
    pure state.definitions.size
private def ty (ctx : LowerContext) (j : Json) (key : String) : Except String MIR.TyId := do
  let j ← field j key
  let id ← natural j "type_id"
  unless ctx.containsTypeId id do throw "instance type references missing compiler metadata"
  pure id
private def kind (ctx : LowerContext) (j : Json) : M CallInstanceKind := do
  match ← str j "kind" with
  | "item" => pure (.Item (← definition j "def_id"))
  | "intrinsic" => pure (.Intrinsic (← definition j "def_id"))
  | "llvm_intrinsic" => pure (.LlvmIntrinsic (← definition j "def_id"))
  | "virtual" => pure (.Virtual (← definition j "def_id") (← natural j "dispatch_slot"))
  | "shim" =>
    let shim : CallShimKind ← do
      match ← str j "shim_kind" with
        | "vtable" => pure (CallShimKind.VTable (← definition j "def_id"))
        | "reify" =>
          let reason ← field j "reason"
          let reason ← if reason == .null then pure none else do
            match ← reason.getStr? with
            | "function_pointer" => pure (some CallReifyReason.FnPtr)
            | "vtable" => pure (some CallReifyReason.Vtable)
            | _ => throw "unknown compiler reify reason"
          pure (.Reify (← definition j "def_id") reason)
        | "fn_pointer" => pure (.FnPtr (← definition j "def_id") (← ty ctx j "function_type"))
        | "closure_once" => pure (.ClosureOnce (← definition j "call_once_def_id") (← definition j "closure_def_id") (← boolean j "track_caller"))
        | "construct_coroutine_in_closure" => pure (.ConstructCoroutineInClosure (← definition j "coroutine_closure_def_id") (← boolean j "receiver_by_ref"))
        | "thread_local" => pure (.ThreadLocal (← definition j "def_id"))
        | "future_drop_poll" => pure (.FutureDropPoll (← definition j "def_id") (← ty ctx j "proxy_coroutine_type") (← ty ctx j "implementation_coroutine_type"))
        | "drop_glue" =>
          let value ← field j "drop_type"
          let dropTy ← if value == .null then pure none else (ty ctx j "drop_type").map some
          pure (.DropGlue (← definition j "def_id") dropTy)
        | "clone" => pure (.Clone (← definition j "def_id") (← ty ctx j "clone_type"))
        | "fn_pointer_as_pointer" => pure (.FnPtrAsPtr (← definition j "def_id") (← ty ctx j "function_type"))
        | "fn_pointer_from_pointer" => pure (.FnPtrFromPtr (← definition j "def_id") (← ty ctx j "function_type"))
        | "async_drop_glue_constructor" => pure (.AsyncDropGlueCtor (← definition j "def_id") (← ty ctx j "drop_type"))
        | "async_drop_glue" => pure (.AsyncDropGlue (← definition j "def_id") (← ty ctx j "coroutine_type"))
        | _ => throw "unknown compiler shim kind"
    pure (.Shim shim)
  | _ => throw "unknown compiler instance kind"

/-- Thread all appended DefId/TypeConstId entries back into the shared bundle. -/
def decodeReference (ctx : LowerContext) (tables : CompilerTables) (j : Json) :
    Except String (CallInstance × CompilerTables) := do
  let (instanceKind, tables) ← (kind ctx (← field j "instance_kind")).run tables
  let args ← ctx.decodeCompilerValue (← field j "generic_args")
  let (args, tables) ← lowerCompilerGenericArgs ctx tables args
  pure (⟨instanceKind, args⟩, tables)

private def bindSource (ctx : LowerContext) (tables : CompilerTables)
    (source : CompilerInstanceSource) : Except String (CallInstance × CompilerTables) := do
  for id in source.requiredTypes do
    unless ctx.containsTypeId id do throw "instance type references missing compiler metadata"
  let mut tables := tables
  let mut definitions : Array MIR.DefId := #[]
  for id in source.definitions do
    match lookupDefinitionId tables.definitions id with
    | .ok index => definitions := definitions.push index
    | .error _ =>
      definitions := definitions.push tables.definitions.size
      tables := { tables with definitions := tables.definitions.push id }
  let definition := fun id => match definitions[id]? with
    | some value => Except.ok value
    | none => Except.error "invalid prepared compiler definition slot"
  let shim : CallShimKind → Except String CallShimKind := fun value => do
    match value with
      | .VTable d => return .VTable (← definition d)
      | .Reify d r => return .Reify (← definition d) r
      | .FnPtr d t => return .FnPtr (← definition d) t
      | .ClosureOnce a b t => return .ClosureOnce (← definition a) (← definition b) t
      | .ConstructCoroutineInClosure d b => return .ConstructCoroutineInClosure (← definition d) b
      | .ThreadLocal d => return .ThreadLocal (← definition d)
      | .FutureDropPoll d p i => return .FutureDropPoll (← definition d) p i
      | .DropGlue d t => return .DropGlue (← definition d) t
      | .Clone d t => return .Clone (← definition d) t
      | .FnPtrAsPtr d t => return .FnPtrAsPtr (← definition d) t
      | .FnPtrFromPtr d t => return .FnPtrFromPtr (← definition d) t
      | .AsyncDropGlueCtor d t => return .AsyncDropGlueCtor (← definition d) t
      | .AsyncDropGlue d t => return .AsyncDropGlue (← definition d) t
  let rebind : CallInstanceKind → Except String CallInstanceKind := fun value => do
    match value with
    | .Item d => return .Item (← definition d)
    | .Intrinsic d => return .Intrinsic (← definition d)
    | .LlvmIntrinsic d => return .LlvmIntrinsic (← definition d)
    | .Virtual d i => return .Virtual (← definition d) i
    | .Shim s => return .Shim (← shim s)
  let kind ← rebind source.kind
  let (args,next) ← lowerCompilerGenericArgs ctx tables source.args
  return (⟨kind,args⟩,next)

/-- Reuse import-time source decoding while rebinding every identity in the
consumer's current tables. Failed source parses retain the original decoder
and first error; changed source fields cannot hit the canonical-key memo. -/
def decode (ctx : LowerContext) (tables : CompilerTables) (j : Json) :
    Except String (CallInstance × CompilerTables) :=
  match ctx.compilerInstanceSourceMemo.bind (·.lookup j) with
  | some source => bindSource ctx tables source
  | none => decodeReference ctx tables j

end Miri.Input.CompilerInstance
