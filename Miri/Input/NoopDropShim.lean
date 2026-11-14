import Miri.Input.MirTemplate

/-! Signature-only constructor for the `DropGlue(_, None)` branch of pinned
rustc_mir_transform/src/shim.rs::build_drop_shim (258–296). This leaf does not
classify a type as having trivial drop, resolve an instance, or construct an ABI.
The caller must establish that exact shim kind; other drop families are absent.
The supported signature binder contains only regions; nested binders and aliases
are outside this first domain. -/
namespace Miri.Input.NoopDropShim
open GenericSubstitution

private def liftPure {m : Type → Type} [Monad m] [MonadExceptOf String m]
    (value : Except String α) : m α :=
  match value with | .ok value => pure value | .error error => throw error

/-- Scoped port of `instantiate_bound_regions_with_erased` from
rustc_middle/src/ty/fold.rs140. No nested binder can occur in this source family;
only regions belonging to the removed outer signature binder are replaced. -/
private def eraseSignatureRegions (variables : Array BoundVariable) :
    Nat → Term → Except String Term
  | 0, _ => .error "no-op drop signature region traversal exhausted"
  | fuel + 1, value => do
    match value with
    | .bound .region (.Bound 0) index _ =>
      let some (.region _) := variables[index]?
        | throw "no-op drop signature region does not belong to its binder"
      pure (.atom .region "erased" "")
    | .bound .. => throw "no-op drop signature has an unsupported bound variable"
    | .binder .. => throw "no-op drop signature excludes nested binders"
    | .node sort tag payload children =>
      pure (.node sort tag payload (← children.mapM (eraseSignatureRegions variables fuel)))
    | .definition sort tag identity children =>
      pure (.definition sort tag identity (← children.mapM (eraseSignatureRegions variables fuel)))
    | _ => pure value

def validateSignature : Term → Except String Unit
  | .binder variables (.node .aggregate "signature" _ (.cons _ (.cons _ .nil))) => do
    unless variables.all (fun boundVar => match boundVar with | .region _ => true | _ => false) do
      throw "no-op drop shim excludes bound type or constant variables"
  | _ => .error "no-op drop shim requires a one-input source signature"

/-- The source signature is an EarlyBinder expression. Its input/output types
are substituted and interned only in the caller's current execution effect. -/
def instantiate {m : Type → Type} [Monad m] [MonadExceptOf String m]
    (fuel : Nat) (sourceSignature : Term) (arguments : Array Term)
    (span : Miri.MIR.SpanRef) (resolveType : Term → m Miri.MIR.TyId) : m Miri.MIR.Body := do
  let signature ← liftPure (GenericSubstitution.instantiate fuel arguments sourceSignature)
  let .binder variables (.node .aggregate "signature" _
      (.cons input (.cons output .nil))) := signature
    | throw "no-op drop shim requires a one-input source signature"
  unless variables.all (fun boundVar => match boundVar with | .region _ => true | _ => false) do
    throw "no-op drop shim excludes bound type or constant variables"
  let resolve (value : Term) := do
    let value ← liftPure (eraseSignatureRegions variables fuel value)
    let value ← liftPure (MirTemplate.eraseFreeRegions fuel value)
    liftPure (MirTemplate.validateClosed fuel value)
    resolveType value
  let output ← resolve output
  let input ← resolve input
  pure {
    phase := .Runtime .Optimized
    argumentCount := 1
    spreadArgument := none
    locals := #[output,input]
    basicBlocks := #[{
      statements := #[]
      terminator := {sourceInfo := {span,scope := 0},kind := .Return}
      cleanup := false }] }

end Miri.Input.NoopDropShim
