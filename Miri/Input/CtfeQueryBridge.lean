import Miri.Input.CompilerTypingEnv
import Miri.Input.InstanceArena
import Miri.Interpreter.CompileTime.RootFinish
/-! Source-to-query orchestration. Callbacks must supply actual World
resolution, normalization/region erasure and CTFE evaluation. This file provides
none of those capabilities and does not admit any production raw Unevaluated. -/
namespace Miri.Input.CtfeQueryBridge
open Miri.Input Miri.MIR CompilerTypingEnv
structure SourceOperand where
  source : UnevaluatedConst
  declaredType : TyId
  usageSpan : Option SpanRef
  deriving Repr
structure GlobalId where
  callee : InstanceArena.Key
  promoted : Option Nat
  deriving Repr, DecidableEq
inductive Family where
  | value | allocation | staticInitializer
  deriving Repr, DecidableEq
/-- Resolved physical callee, before invalidating rigid aliases and region erasure. -/
structure ResolvedInput where
  family : Family
  environment : Env
  global : GlobalId
  deriving Repr, DecidableEq
/-- Provider input after pinned normalization and region-erasure processing. -/
structure QueryKey where
  family : Family
  environment : Env
  global : GlobalId
  deriving Repr, DecidableEq
inductive Failure (Diagnostic : Type) where
  | tooGeneric (span : Option SpanRef)
  | reported (diagnostic : Diagnostic) (span : Option SpanRef)
  | unsupported (reason : String)
  | internal (reason : String)
  deriving Repr
/-- Results retain the execution World on success and failure. -/
abbrev Action (World Diagnostic Value : Type) := World → Except (Failure Diagnostic) Value × World
structure Access (World Diagnostic Value : Type) where
  /-- Includes pinned non-region-inference invariant checks. -/
  validate : SourceOperand → Action World Diagnostic Unit
  /-- Instance::try_resolve, including associated-constant implementation selection. -/
  resolve : Env → UnevaluatedConst → Action World Diagnostic (Option InstanceArena.Key)
  /-- with_post_analysis_normalized_invalidating_rigid_aliases then erase_and_anonymize_regions. -/
  queryInput : ResolvedInput → Action World Diagnostic QueryKey
  /-- Memoized raw value provider, including distinct allocation-query semantics. -/
  evaluate : QueryKey → Action World Diagnostic Value
/-- Explicit allocated-root provider stages. executeRoot must perform the real
layout/allocation/raw-frame/body operations before returning an opaque root.
There is no default allocator and no scalar-candidate-to-root conversion. -/
structure AllocatedRootAccess (World Diagnostic Root Value : Type) where
  executeRoot : QueryKey → Action World Diagnostic Root
  intern : QueryKey → Root → World → Except Interpreter.CompileTime.RootFinish.InternError Unit × World
  validateRoot : QueryKey → Root → Action World Diagnostic Unit
  reportIntern : QueryKey → Interpreter.CompileTime.RootFinish.InternError → World → Failure Diagnostic × World
  makeResult : QueryKey → Root → World → Value × World

/-- Compose genuine root capabilities through the pinned finish order. Missing
allocator/validator capabilities must fail through executeRoot, never fabricate
an allocated root or return a source-frame candidate as a compiler answer. -/
def evaluateAllocatedRoot (access : AllocatedRootAccess W D R V) (key : QueryKey) : Action W D V := fun world =>
  let (executed,world) := access.executeRoot key world
  match executed with
  | .error error => (.error error,world)
  | .ok root =>
    match Interpreter.CompileTime.RootFinish.finish (access.intern key) (access.validateRoot key)
        (access.reportIntern key) (access.makeResult key) root world with
    | .returned value world => (.ok value,world)
    | .failed _ error world => (.error error,world)

/-- The public source-to-query bridge uses the same finish controller when a
caller supplies real allocated-root capabilities. No such production allocator
is installed by this adapter. -/
def Access.withAllocatedRoots (access : Access W D V) (roots : AllocatedRootAccess W D R V) : Access W D V :=
  {access with evaluate := evaluateAllocatedRoot roots}

private def resolutionFailure : Failure D → Failure D
  | .tooGeneric _ => .tooGeneric none
  | .reported diagnostic _ => .reported diagnostic none
  | other => other
private def atUsage (span : Option SpanRef) : Failure D → Failure D
  | .tooGeneric previous => .tooGeneric (span.orElse (fun _ => previous))
  | .reported diagnostic previous => .reported diagnostic (span.orElse (fun _ => previous))
  | other => other

def evaluate (access : Access W D V) (environment : Env) (operand : SourceOperand) : Action W D V := fun world => Id.run do
  let (validation,world) := access.validate operand world
  if let .error error := validation then return (.error error,world)
  let (resolution,world) := access.resolve environment operand.source world
  let callee ← match resolution with
    | .error error => return (.error (resolutionFailure error),world)
    | .ok none => return (.error (.tooGeneric none),world)
    | .ok (some callee) => pure callee
  let proposed := ResolvedInput.mk .value environment ⟨callee,operand.source.promoted⟩
  let (input,world) := access.queryInput proposed world
  let key ← match input with
    | .error error => return (.error error,world)
    | .ok key => pure key
  unless key.family == proposed.family && key.global.promoted == proposed.global.promoted &&
      key.global.callee.definition == proposed.global.callee.definition do
    return (.error (.internal "CTFE query canonicalization changed physical root/promoted identity or query family"),world)
  let (value,world) := access.evaluate key world
  return (value.mapError (atUsage operand.usageSpan),world)
end Miri.Input.CtfeQueryBridge
