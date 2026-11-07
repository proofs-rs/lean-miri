import Miri.Input.Reader.Catalog
import Miri.MIR.Syntax

namespace Miri.Input.Reader
open Lean Miri.MIR

def Catalog.mutability (catalog : Catalog) (input : Json) (path : String) : Except String Mutability := do
  match ← catalog.string (← catalog.field input "kind" path) path with
  | "mutable" => return .Mut
  | "immutable" => return .Not
  | kind => throw s!"{path}: unsupported mutability {kind}"

private def safety (catalog : Catalog) (input : Json) (path : String) : Except String Safety := do
  match ← catalog.string (← catalog.field input "kind" path) path with
  | "safe" => return .Safe
  | "unsafe" => return .Unsafe
  | kind => throw s!"{path}: unsupported safety {kind}"

def Catalog.castKind (catalog : Catalog) (input : Json) (path : String) : Except String CastKind := do
  let field := fun key => catalog.field input key path
  match ← catalog.string (← field "kind") path with
  | "PointerExposeProvenance" => return .PointerExposeProvenance
  | "PointerWithExposedProvenance" => return .PointerWithExposedProvenance
  | "PointerCoercion" =>
    let input ← field "coercion"
    let coercion ← (show Except String PointerCoercion from do
      match ← catalog.string (← catalog.field input "kind" path) path with
      | "ReifyFnPointer" => return .ReifyFnPointer (← safety catalog (← catalog.field input "safety" path) path)
      | "UnsafeFnPointer" => return .UnsafeFnPointer
      | "ClosureFnPointer" => return .ClosureFnPointer (← safety catalog (← catalog.field input "safety" path) path)
      | "MutToConstPointer" => return .MutToConstPointer
      | "ArrayToPointer" => return .ArrayToPointer
      | "Unsize" => return .Unsize
      | kind => throw s!"{path}: unsupported pointer coercion {kind}")
    let source ← match ← catalog.string (← catalog.field (← field "source") "kind" path) path with
      | "as_cast" => pure CoercionSource.AsCast
      | "implicit" => pure .Implicit
      | kind => throw s!"{path}: unsupported coercion source {kind}"
    return .PointerCoercion coercion source
  | "IntToInt" => return .IntToInt
  | "FloatToInt" => return .FloatToInt
  | "FloatToFloat" => return .FloatToFloat
  | "IntToFloat" => return .IntToFloat
  | "PtrToPtr" => return .PtrToPtr
  | "FnPtrToPtr" => return .FnPtrToPtr
  | "Transmute" => return .Transmute
  | "BoxDerefTransmute" => return .BoxDerefTransmute
  | "Subtype" => return .Subtype
  | kind => throw s!"{path}: unsupported cast kind {kind}"

def Catalog.borrowKind (catalog : Catalog) (input : Json) (path : String) : Except String BorrowKind := do
  let field := fun key => catalog.field input key path
  match ← catalog.string (← field "kind") path with
  | "shared" => return .Shared
  | "fake" =>
    match ← catalog.string (← field "fake_kind") path with
    | "shallow" => return .Fake .Shallow
    | "deep" => return .Fake .Deep
    | kind => throw s!"{path}: unsupported fake borrow {kind}"
  | "mutable" =>
    match ← catalog.string (← field "mutability_kind") path with
    | "default" => return .Mut .Default
    | "two_phase" => return .Mut .TwoPhaseBorrow
    | "closure_capture" => return .Mut .ClosureCapture
    | kind => throw s!"{path}: unsupported mutable borrow {kind}"
  | kind => throw s!"{path}: unsupported borrow kind {kind}"

def Catalog.unwindReason (catalog : Catalog) (input : Json) (path : String) : Except String UnwindTerminateReason := do
  match ← catalog.string (← catalog.field input "kind" path) path with
  | "abi" => return .Abi
  | "in_cleanup" => return .InCleanup
  | kind => throw s!"{path}: unsupported unwind reason {kind}"

def Catalog.unwind (catalog : Catalog) (input : Json) (path : String) : Except String UnwindAction := do
  match ← catalog.string (← catalog.field input "kind" path) path with
  | "Continue" => return .Continue
  | "Unreachable" => return .Unreachable
  | "Cleanup" => return .Cleanup (← catalog.natural (← catalog.field input "target" path) path)
  | "Terminate" => return .Terminate (← catalog.unwindReason (← catalog.field input "reason" path) path)
  | kind => throw s!"{path}: unsupported unwind action {kind}"

def Catalog.coroutine (catalog : Catalog) (input : Json) (path : String) : Except String CoroutineKind := do
  let field := fun key => catalog.field input key path
  let text := fun key => do catalog.string (← field key) path
  match ← text "kind" with
  | "desugared" =>
    let desugaring ← match ← text "desugaring" with
      | "async" => pure CoroutineDesugaring.Async
      | "gen" => pure .Gen
      | "async_gen" => pure .AsyncGen
      | kind => throw s!"{path}: unsupported coroutine desugaring {kind}"
    let source ← match ← text "source" with
      | "block" => pure CoroutineSource.Block
      | "closure" => pure .Closure
      | "function" => pure .Fn
      | kind => throw s!"{path}: unsupported coroutine source {kind}"
    return .Desugared desugaring source
  | "coroutine" =>
    match ← text "movability" with
    | "static" => return .Coroutine .Static
    | "movable" => return .Coroutine .Movable
    | kind => throw s!"{path}: unsupported coroutine movability {kind}"
  | kind => throw s!"{path}: unsupported coroutine kind {kind}"

def Catalog.loopHint (catalog : Catalog) (input : Json) (path : String) : Except String LoopHintAttr := do
  match ← catalog.string (← catalog.field input "kind" path) path with
  | "Hint" => return .Hint
  | "Full" => return .Full
  | "Never" => return .Never
  | "Count" => return .Count (← catalog.natural (← catalog.field input "count" path) path)
  | kind => throw s!"{path}: unsupported loop hint {kind}"

def Catalog.callSource (catalog : Catalog) (input : Json) (path : String) : Except String CallSource := do
  match ← catalog.string (← catalog.field input "kind" path) path with
  | "overloaded_operator" => return .OverloadedOperator
  | "match_comparison" => return .MatchCmp
  | "miscellaneous_desugaring" => return .Misc
  | "clone_or_use" => return .Use
  | "normal_call" => return .Normal
  | kind => throw s!"{path}: unsupported call source {kind}"

end Miri.Input.Reader
