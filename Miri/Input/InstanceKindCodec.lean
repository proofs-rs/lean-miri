import Miri.Input.JsonReader
import Miri.Interpreter.Instance

namespace Miri.Input.InstanceKindCodec
open JsonReader

open Miri.Interpreter

private structure decodeFields where
  «call_once_def_id» : Option (Nat) := none
  «clone_type» : Option (Nat) := none
  «closure_def_id» : Option (Nat) := none
  «coroutine_closure_def_id» : Option (Nat) := none
  «coroutine_type» : Option (Nat) := none
  «def_id» : Option (Nat) := none
  «dispatch_slot» : Option (Nat) := none
  «drop_type» : Option (Option Nat) := none
  «function_type» : Option (Nat) := none
  «implementation_coroutine_type» : Option (Nat) := none
  «kind» : Option (String) := none
  «proxy_coroutine_type» : Option (Nat) := none
  «reason» : Option (Option String) := none
  «receiver_by_ref» : Option (Bool) := none
  «shim_kind» : Option (String) := none
  «track_caller» : Option (Bool) := none

def decode  : Parser (CallInstanceKind) := do
  let s ← object (decodeFields.mk none none none none none none none none none none none none none none none none) fun s key => do
    match key with
    | "call_once_def_id" => return { s with «call_once_def_id» := some (← natural) }
    | "clone_type" => return { s with «clone_type» := some (← natural) }
    | "closure_def_id" => return { s with «closure_def_id» := some (← natural) }
    | "coroutine_closure_def_id" => return { s with «coroutine_closure_def_id» := some (← natural) }
    | "coroutine_type" => return { s with «coroutine_type» := some (← natural) }
    | "def_id" => return { s with «def_id» := some (← natural) }
    | "dispatch_slot" => return { s with «dispatch_slot» := some (← natural) }
    | "drop_type" => return { s with «drop_type» := some (← nullable natural) }
    | "function_type" => return { s with «function_type» := some (← natural) }
    | "implementation_coroutine_type" => return { s with «implementation_coroutine_type» := some (← natural) }
    | "kind" => return { s with «kind» := some (← string) }
    | "proxy_coroutine_type" => return { s with «proxy_coroutine_type» := some (← natural) }
    | "reason" => return { s with «reason» := some (← nullable string) }
    | "receiver_by_ref" => return { s with «receiver_by_ref» := some (← boolean) }
    | "shim_kind" => return { s with «shim_kind» := some (← string) }
    | "track_caller" => return { s with «track_caller» := some (← boolean) }
    | _ => skipValue; pure s
  let variant ← required s.«kind» "kind"
  if s.«dispatch_slot».isSome && variant != "virtual" then fail "dispatch_slot is only valid for virtual instances"
  if variant != "shim" && (s.«shim_kind».isSome || s.«reason».isSome || s.«function_type».isSome || s.«call_once_def_id».isSome || s.«closure_def_id».isSome || s.«track_caller».isSome || s.«coroutine_closure_def_id».isSome || s.«receiver_by_ref».isSome || s.«proxy_coroutine_type».isSome || s.«implementation_coroutine_type».isSome || s.«drop_type».isSome || s.«clone_type».isSome || s.«coroutine_type».isSome) then fail "shim payload in non-shim instance"
  if variant == "shim" then
    let shim ← required s.«shim_kind» "shim_kind"
    if s.«reason».isSome && !(shim == "reify") then fail s!"incompatible field `reason` for shim `{shim}`"
    if s.«function_type».isSome && !(shim == "fn_pointer" || shim == "fn_pointer_as_pointer" || shim == "fn_pointer_from_pointer") then fail s!"incompatible field `function_type` for shim `{shim}`"
    if s.«call_once_def_id».isSome && !(shim == "closure_once") then fail s!"incompatible field `call_once_def_id` for shim `{shim}`"
    if s.«closure_def_id».isSome && !(shim == "closure_once") then fail s!"incompatible field `closure_def_id` for shim `{shim}`"
    if s.«track_caller».isSome && !(shim == "closure_once") then fail s!"incompatible field `track_caller` for shim `{shim}`"
    if s.«coroutine_closure_def_id».isSome && !(shim == "construct_coroutine_in_closure") then fail s!"incompatible field `coroutine_closure_def_id` for shim `{shim}`"
    if s.«receiver_by_ref».isSome && !(shim == "construct_coroutine_in_closure") then fail s!"incompatible field `receiver_by_ref` for shim `{shim}`"
    if s.«proxy_coroutine_type».isSome && !(shim == "future_drop_poll") then fail s!"incompatible field `proxy_coroutine_type` for shim `{shim}`"
    if s.«implementation_coroutine_type».isSome && !(shim == "future_drop_poll") then fail s!"incompatible field `implementation_coroutine_type` for shim `{shim}`"
    if s.«drop_type».isSome && !(shim == "drop_glue" || shim == "async_drop_glue_constructor") then fail s!"incompatible field `drop_type` for shim `{shim}`"
    if s.«clone_type».isSome && !(shim == "clone") then fail s!"incompatible field `clone_type` for shim `{shim}`"
    if s.«coroutine_type».isSome && !(shim == "async_drop_glue") then fail s!"incompatible field `coroutine_type` for shim `{shim}`"
    if s.«def_id».isSome && !(shim == "vtable" || shim == "reify" || shim == "fn_pointer" || shim == "thread_local" || shim == "future_drop_poll" || shim == "drop_glue" || shim == "clone" || shim == "fn_pointer_as_pointer" || shim == "fn_pointer_from_pointer" || shim == "async_drop_glue_constructor" || shim == "async_drop_glue") then fail s!"incompatible field `def_id` for shim `{shim}`"
  match (← required s.«kind» "kind") with
  | "item" => pure (.Item ((← required s.«def_id» "def_id")))
  | "intrinsic" => pure (.Intrinsic ((← required s.«def_id» "def_id")))
  | "llvm_intrinsic" => pure (.LlvmIntrinsic ((← required s.«def_id» "def_id")))
  | "virtual" => pure (.Virtual ((← required s.«def_id» "def_id")) ((← required s.«dispatch_slot» "dispatch_slot")))
  | "shim" =>
    let shim : CallShimKind ← do
      match (← required s.«shim_kind» "shim_kind") with
        | "vtable" => pure (CallShimKind.VTable ((← required s.«def_id» "def_id")))
        | "reify" =>
          let reason := (← required s.«reason» "reason")
          let reason ← if reason.isNone then pure none else do
            match ← required reason "reason" with
            | "function_pointer" => pure (some CallReifyReason.FnPtr)
            | "vtable" => pure (some CallReifyReason.Vtable)
            | _ => fail "unknown compiler reify reason"
          pure (.Reify ((← required s.«def_id» "def_id")) reason)
        | "fn_pointer" => pure (.FnPtr ((← required s.«def_id» "def_id")) ((← required s.«function_type» "function_type")))
        | "closure_once" => pure (.ClosureOnce ((← required s.«call_once_def_id» "call_once_def_id")) ((← required s.«closure_def_id» "closure_def_id")) ((← required s.«track_caller» "track_caller")))
        | "construct_coroutine_in_closure" => pure (.ConstructCoroutineInClosure ((← required s.«coroutine_closure_def_id» "coroutine_closure_def_id")) ((← required s.«receiver_by_ref» "receiver_by_ref")))
        | "thread_local" => pure (.ThreadLocal ((← required s.«def_id» "def_id")))
        | "future_drop_poll" => pure (.FutureDropPoll ((← required s.«def_id» "def_id")) ((← required s.«proxy_coroutine_type» "proxy_coroutine_type")) ((← required s.«implementation_coroutine_type» "implementation_coroutine_type")))
        | "drop_glue" =>
          let dropTy := (← required s.«drop_type» "drop_type")
          pure (.DropGlue ((← required s.«def_id» "def_id")) dropTy)
        | "clone" => pure (.Clone ((← required s.«def_id» "def_id")) ((← required s.«clone_type» "clone_type")))
        | "fn_pointer_as_pointer" => pure (.FnPtrAsPtr ((← required s.«def_id» "def_id")) ((← required s.«function_type» "function_type")))
        | "fn_pointer_from_pointer" => pure (.FnPtrFromPtr ((← required s.«def_id» "def_id")) ((← required s.«function_type» "function_type")))
        | "async_drop_glue_constructor" => pure (.AsyncDropGlueCtor ((← required s.«def_id» "def_id")) ((← required (← required s.«drop_type» "drop_type") "drop_type")))
        | "async_drop_glue" => pure (.AsyncDropGlue ((← required s.«def_id» "def_id")) ((← required s.«coroutine_type» "coroutine_type")))
        | _ => fail "unknown compiler shim kind"
    pure (.Shim shim)
  | _ => fail "unknown compiler instance kind"

end Miri.Input.InstanceKindCodec
