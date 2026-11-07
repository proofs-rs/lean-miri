import Miri.Input.Reader.Generics
import Miri.Interpreter.Instance

namespace Miri.Input.Reader.InstanceReader
open Lean Miri.MIR Miri.Interpreter
abbrev Decode := MIRReader.Decode

private def typeId (catalog : Catalog) (count : Nat) (input : Json) (path : String) : Except String TyId := do
  let id ← catalog.natural (← catalog.field input "type_id" path) path
  unless id < count do throw s!"{path}: invalid instance type ID {id}"
  return id

private def kind (catalog : Catalog) (count : Nat) (input : Json) (path : String) : Decode CallInstanceKind := do
  let field := fun key => catalog.field input key path
  let definition := fun key => do GenericReader.definition catalog (← field key) path
  let ty := fun key => do typeId catalog count (← field key) path
  let boolean := fun key => do catalog.boolean (← field key) path
  match ← catalog.string (← field "kind") path with
  | "item" => return .Item (← definition "def_id")
  | "intrinsic" => return .Intrinsic (← definition "def_id")
  | "llvm_intrinsic" => return .LlvmIntrinsic (← definition "def_id")
  | "virtual" => return .Virtual (← definition "def_id") (← catalog.natural (← field "dispatch_slot") path)
  | "shim" =>
    let shim ← (show Decode CallShimKind from do
      match ← catalog.string (← field "shim_kind") path with
      | "vtable" => return .VTable (← definition "def_id")
      | "reify" =>
        let reason ← catalog.inspect (← field "reason") path
        let reason ← if reason == .null then pure none else do
          match ← catalog.string reason path with
          | "function_pointer" => pure (some CallReifyReason.FnPtr)
          | "vtable" => pure (some .Vtable)
          | kind => throw s!"{path}: unsupported reify reason {kind}"
        return .Reify (← definition "def_id") reason
      | "fn_pointer" => return .FnPtr (← definition "def_id") (← ty "function_type")
      | "closure_once" => return .ClosureOnce (← definition "call_once_def_id") (← definition "closure_def_id") (← boolean "track_caller")
      | "construct_coroutine_in_closure" => return .ConstructCoroutineInClosure (← definition "coroutine_closure_def_id") (← boolean "receiver_by_ref")
      | "thread_local" => return .ThreadLocal (← definition "def_id")
      | "future_drop_poll" => return .FutureDropPoll (← definition "def_id") (← ty "proxy_coroutine_type") (← ty "implementation_coroutine_type")
      | "drop_glue" =>
        let input ← catalog.inspect (← field "drop_type") path
        let dropType ← if input == .null then pure none else some <$> typeId catalog count input path
        return .DropGlue (← definition "def_id") dropType
      | "clone" => return .Clone (← definition "def_id") (← ty "clone_type")
      | "fn_pointer_as_pointer" => return .FnPtrAsPtr (← definition "def_id") (← ty "function_type")
      | "fn_pointer_from_pointer" => return .FnPtrFromPtr (← definition "def_id") (← ty "function_type")
      | "async_drop_glue_constructor" => return .AsyncDropGlueCtor (← definition "def_id") (← ty "drop_type")
      | "async_drop_glue" => return .AsyncDropGlue (← definition "def_id") (← ty "coroutine_type")
      | kind => throw s!"{path}: unsupported shim kind {kind}")
    return .Shim shim
  | kind => throw s!"{path}: unsupported instance kind {kind}"

def read (catalog : Catalog) (count : Nat) (input : Json) (path : String) : Decode CallInstance := do
  let kind ← kind catalog count (← catalog.field input "instance_kind" path) path
  let id ← GenericReader.arguments catalog count (← catalog.field input "generic_args" path) path
  let state ← get
  let args ← state.arguments.lookup id |>.mapError (fun id => s!"{path}: generic argument list {id} absent")
  return ⟨kind,args⟩

end Miri.Input.Reader.InstanceReader
