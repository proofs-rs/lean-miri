import Miri.Input.JsonReader
import Miri.Interpreter.Instance

/-! A single canonical instance row's typed kind. Definitions and types remain
serialization-local numeric references; validation checks their table bounds. -/
namespace Miri.Input.InstanceKindCodec
open Lean Miri.Interpreter
private def field [JsonReader.FieldSource α] (j : α) (key : String) : Except String JsonReader.Slice := JsonReader.FieldSource.lookupField j key
private def str [JsonReader.FieldSource α] (j : α) (key : String) : Except String String := do (← field j key).string
private def boolean [JsonReader.FieldSource α] (j : α) (key : String) : Except String Bool := do (← field j key).boolean
private def natural [JsonReader.FieldSource α] (j : α) (key : String) : Except String Nat := do (← field j key).natural
private def definition [JsonReader.FieldSource α] (j : α) (key : String) : Except String MIR.DefId :=
  natural j key
private def ty [JsonReader.FieldSource α] (j : α) (key : String) : Except String MIR.TyId :=
  natural j key
def decode (j : JsonReader.Slice) : Except String CallInstanceKind := do
  let j ← j.view
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
          let reason ← if reason.isNull then pure none else do
            match ← reason.string with
            | "function_pointer" => pure (some CallReifyReason.FnPtr)
            | "vtable" => pure (some CallReifyReason.Vtable)
            | _ => throw "unknown compiler reify reason"
          pure (.Reify (← definition j "def_id") reason)
        | "fn_pointer" => pure (.FnPtr (← definition j "def_id") (← ty j "function_type"))
        | "closure_once" => pure (.ClosureOnce (← definition j "call_once_def_id") (← definition j "closure_def_id") (← boolean j "track_caller"))
        | "construct_coroutine_in_closure" => pure (.ConstructCoroutineInClosure (← definition j "coroutine_closure_def_id") (← boolean j "receiver_by_ref"))
        | "thread_local" => pure (.ThreadLocal (← definition j "def_id"))
        | "future_drop_poll" => pure (.FutureDropPoll (← definition j "def_id") (← ty j "proxy_coroutine_type") (← ty j "implementation_coroutine_type"))
        | "drop_glue" =>
          let value ← field j "drop_type"
          let dropTy ← if value.isNull then pure none else (ty j "drop_type").map some
          pure (.DropGlue (← definition j "def_id") dropTy)
        | "clone" => pure (.Clone (← definition j "def_id") (← ty j "clone_type"))
        | "fn_pointer_as_pointer" => pure (.FnPtrAsPtr (← definition j "def_id") (← ty j "function_type"))
        | "fn_pointer_from_pointer" => pure (.FnPtrFromPtr (← definition j "def_id") (← ty j "function_type"))
        | "async_drop_glue_constructor" => pure (.AsyncDropGlueCtor (← definition j "def_id") (← ty j "drop_type"))
        | "async_drop_glue" => pure (.AsyncDropGlue (← definition j "def_id") (← ty j "coroutine_type"))
        | _ => throw "unknown compiler shim kind"
    pure (.Shim shim)
  | _ => throw "unknown compiler instance kind"


end Miri.Input.InstanceKindCodec
