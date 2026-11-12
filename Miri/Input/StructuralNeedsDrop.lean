import Miri.Input.Model.Types

/-! Synchronous `Ty::needs_drop` for monomorphic material types, pinned rustc
8144389c895da997dbdecaa635e41d6a50be6ffd:
`rustc_middle/src/ty/util.rs::needs_drop_components_with_async` and
`rustc_ty_utils/src/needs_drop.rs::{needs_drop_raw, drop_tys_helper}`.

`shape` must resolve the pinned normalization operation before supplying a node.
ADT fields are already instantiated material types. The `Copy` guard in the
upstream iterator cannot suppress a destructor or a field needing synchronous
drop in a well-formed monomorphic ADT; rustc rejects those Copy implementations.
ManuallyDrop is identified by its lang-item definition flag, never by its name.
Unions, including MaybeUninit, do not recursively drop fields. Destructor IDs
are material impl identities, rather than a precomputed needs_drop answer.

`none` is an unresolved component, not `false`; it requires residual semantic
support. Missing material and fuel exhaustion remain errors. This module does
not yet port unsafe-binder instantiation or unresolved aliases. -/
namespace Miri.Input.StructuralNeedsDrop

abbrev AdtMaterial := AdtDropMaterial

/-- Combine independent components without treating an unresolved component as
no drop. A known synchronous destructor makes the result true. -/
def combine (left right : Option Bool) : Option Bool :=
  match left, right with
  | some true, _ | _, some true => some true
  | some false, some false => some false
  | _, _ => none

/-- Pinned generic_args.rs::split_{closure,coroutine_closure}_args:
all synthetic arguments are types; the capture tuple is last for Closure and
second-last for CoroutineClosure. Generic parent arguments are retained. -/
private def captures (args : Array Miri.MIR.GenericArg) (synthetics trailing : Nat) :
    Except String TypeId := do
  unless args.size >= synthetics do throw "closure arguments missing synthetics"
  unless (args.toList.drop (args.size - synthetics)).all (fun arg =>
      match arg with | .Type _ => true | _ => false) do
    throw "closure synthetic argument is not a type"
  let some (.Type tuple) := args[args.size - trailing]?
    | throw "closure capture tuple type absent"
  pure tuple

private def visit (shape : TypeId → Except String TypeShape)
    (adt : DefinitionRef → Except String AdtMaterial) :
    Nat → TypeId → StateT (Array (TypeId × Option Bool)) (Except String) (Option Bool)
  | 0, _ => throw "structural needs_drop recursion exhausted"
  | fuel + 1, ty => do
    if let some (_, result) := (← get).find? (·.1 == ty) then return result
    let result ← do
      let source ← liftM (shape ty)
      match source with
      | .int _ | .uint _ | .float _ | .bool | .char | .str | .never
      | .reference .. | .rawPointer .. | .functionDefinition .. | .functionPointer ..
      | .foreign _ => pure (some false)
      | .dynamicTraitObject .. | .coroutine .. => pure (some true)
      | .closure _ args _ | .coroutineClosure _ args => do
        let isCoroutineClosure := source.kind == .coroutineClosure
        let tuple ← liftM (captures args (if isCoroutineClosure then 4 else 3)
          (if isCoroutineClosure then 2 else 1))
        let .tuple _ ← liftM (shape tuple)
          | throw "closure upvar material is not a tuple"
        visit shape adt fuel tuple
      | .tuple fields => do
        let mut result := some false
        for field in fields do
          result := combine result (← visit shape adt fuel field)
        pure result
      | .patternType inner _ | .slice inner => visit shape adt fuel inner
      | .array inner _ constructor => do
        if constructor.count == 0 then return some false
        visit shape adt fuel inner
      | .adt data => do
        let material ← liftM (adt data.definition)
        if material.manuallyDrop then return some false
        if material.destructor.isSome then return some true
        if data.kind == .unionKind then return some false
        let mut result := some false
        for variant in data.variants do
          for field in variant.fields do
            result := combine result (← visit shape adt fuel field.typeId)
        pure result
      | _ => pure none
    modify (·.push (ty, result))
    pure result

/-- Demand-local memoization avoids exponential traversal of shared type graphs.
The cache is freshly allocated for each query; no compiler or guest state is
shared between executions. Errors are never cached as successful answers. -/
def query (shape : TypeId → Except String TypeShape)
    (adt : DefinitionRef → Except String AdtMaterial) (fuel : Nat) (ty : TypeId) :
    Except String (Option Bool) :=
  (visit shape adt fuel ty #[]).map (·.1)

end Miri.Input.StructuralNeedsDrop
