import Miri.Input.GenericInstantiation
import Miri.Input.MirDirectCall

/-! Ordinary source-call identity reconstruction. This leaf consumes immutable
raw definition/instance/type material; it does not read call-site resolution
answers. ABI and transfer queries are intentionally separate residual providers.
Only binder-free, type-only ordinary function callees belong to this category.
Production call preparation is not connected to this leaf yet. -/
namespace Miri.Input.SourceCall
open GenericSubstitution

structure Resolution where
  instanceId : InstanceId
  functionType : TypeId
  arguments : Array Miri.MIR.GenericArg
  deriving Repr

def resolveTypeArgumentsWith {m : Type → Type} [Monad m] [MonadExceptOf String m]
    (resolveType : Term → m TypeId) (arguments : Array Term) : m (Array Miri.MIR.GenericArg) :=
  arguments.mapM fun argument => do
    unless argument.sort == .type do
      throw "ordinary source call currently requires type-only generic arguments"
    pure (.Type (← resolveType argument))

def functionTerm (callee : MirDirectCall.Callee) : Term :=
  .definition .type "function_definition" callee.definition
    (.cons (.binder #[] (.node .aggregate "arguments" "" callee.arguments)) .nil)

private def argumentArray (result : Array Term) : Terms → Array Term
  | .nil => result
  | .cons head tail => argumentArray (result.push head) tail

def calleeOfFunctionTerm : Term → Except String MirDirectCall.Callee
  | .definition .type "function_definition" definition
      (.cons (.binder variables (.node .aggregate "arguments" "" arguments)) .nil) => do
    unless variables.isEmpty do throw "ordinary source call excludes bound FnDef arguments"
    pure ⟨definition,argumentArray #[] arguments⟩
  | _ => .error "ordinary source call requires exact FnDef source structure"

/-- All callbacks inhabit the same effect. Execution integration must use its
one owned universe here, retaining newly interned argument and FnDef identities.
Instance construction is a separate capability, never inferred from layout. -/
def resolveCalleeWith {m : Type → Type} [Monad m] [MonadExceptOf String m]
    (resolveDefinition : DefinitionIdentity → m DefinitionRef)
    (resolveType : Term → m TypeId)
    (resolveInstance : DefinitionRef → Array Miri.MIR.GenericArg → m InstanceId)
    (callee : MirDirectCall.Callee) : m Resolution := do
  let definition ← resolveDefinition callee.definition
  let arguments ← resolveTypeArgumentsWith resolveType callee.arguments
  let instanceId ← resolveInstance definition arguments
  let functionType ← resolveType (functionTerm callee)
  pure ⟨instanceId,functionType,arguments⟩

/-- Explicit remaining material instance-graph lookup. This cannot construct a
novel complete instance, body or ABI; an absent identity remains an error. -/
def materialItem (document : ImportDocument) (definition : DefinitionRef)
    (arguments : Array Miri.MIR.GenericArg) : Except String InstanceId := do
  let mut found := none
  for (candidate,index) in document.instances.zipIdx do
    if candidate.instanceKind == .Item definition && candidate.genericArgs == arguments then
      unless found.isNone do throw "duplicate exact ordinary source-call Item identity"
      unless candidate.id == index do throw "ordinary source-call instance ID/index mismatch"
      found := some candidate.id
  let some instanceId := found | throw "ordinary source-call Item material is absent"
  pure instanceId

/-- Material-only differential driver. Runtime integration uses
`resolveCalleeWith` with execution-owned state instead of this closed context. -/
def resolveCallee (document : ImportDocument) (fuel : Nat)
    (callee : MirDirectCall.Callee) : Except String Resolution := do
  let context ← GenericInstantiation.Context.ofDocument document
  resolveCalleeWith (GenericInstantiation.definitionRef context)
    (GenericInstantiation.resolveType context fuel) (materialItem document) callee

end Miri.Input.SourceCall
