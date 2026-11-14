import Miri.Input.RawFunctionSignature
import Miri.Input.MirTemplate

/-! Source constructors for pinned shim.rs::build_fn_ptr_{as,from}_ptr_shim.
The raw source method signature owns the local types; this module neither
queries a compiler body nor stores a constructed body or ABI answer. -/
namespace Miri.Input.FnPointerShim
open GenericSubstitution

inductive Direction where
  | asPointer | fromPointer
  deriving Repr, DecidableEq

private def liftPure {m : Type → Type} [Monad m] [MonadExceptOf String m]
    (value : Except String α) : m α :=
  match value with | .ok value => pure value | .error error => throw error

/-- Build the final interpreter-visible MIR of the pinned FnPtr conversion
shim. Its outer signature has no bound variables; the pointed-to function's
own complete signature is retained inside `selfType`. -/
def instantiate {m : Type → Type} [Monad m] [MonadExceptOf String m]
    (fuel : Nat) (direction : Direction) (sourceSignature selfType nonNullType : Term)
    (span : Miri.MIR.SpanRef) (resolveType : Term → m Miri.MIR.TyId) : m Miri.MIR.Body := do
  let .node .type "function_pointer" _ _ := selfType
    | throw "FnPtr conversion shim requires a function-pointer self type"
  let signature ← liftPure (GenericSubstitution.instantiate fuel #[selfType] sourceSignature)
  let signature ← liftPure (RawFunctionSignature.read signature)
  unless signature.variables.isEmpty && signature.inputs.size == 1 do
    throw "FnPtr conversion shim requires a binder-free one-input source signature"
  unless signature.abi == .Rust && !signature.cVariadic && signature.splatted.isNone do
    throw "FnPtr conversion method requires the pinned Rust source header"
  let some input := signature.inputs[0]? | throw "FnPtr conversion input disappeared"
  match direction with
  | .asPointer =>
    unless signature.safety == .Safe && input == selfType && signature.output == nonNullType do
      throw "FnPtr::as_ptr raw signature does not match Self and NonNull<Code>"
  | .fromPointer =>
    unless signature.safety == .Unsafe && input == nonNullType && signature.output == selfType do
      throw "FnPtr::from_ptr raw signature does not match NonNull<Code> and Self"
  let output ← resolveType signature.output
  let input ← resolveType input
  let info : Miri.MIR.SourceInfo := ⟨span,0⟩
  let assign (destination operand : Nat) (kind : Miri.MIR.CastKind) (target : Nat) : Miri.MIR.Statement :=
    ⟨info,.Assign ⟨destination,#[]⟩ (.Cast kind (.Move ⟨operand,#[]⟩) target)⟩
  let (locals,statements) ← match direction with
    | .fromPointer => pure (#[output,input],#[assign 0 1 .Transmute output])
    | .asPointer => do
      let unit := Term.node .type "tuple" "" .nil
      let rawPointer := Term.node .type "raw_pointer" "immutable" (.cons unit .nil)
      let rawPointer ← resolveType rawPointer
      pure (#[output,input,rawPointer],#[assign 2 1 .FnPtrToPtr rawPointer,assign 0 2 .Transmute output])
  pure {
    phase := .Runtime .Optimized
    argumentCount := 1
    spreadArgument := none
    locals
    basicBlocks := #[{statements,terminator := ⟨info,.Return⟩,cleanup := false}] }

end Miri.Input.FnPointerShim
