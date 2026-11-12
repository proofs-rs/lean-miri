import Miri.Input.Model.Types

namespace Miri.Input

/-- Compiler-owned auxiliary MIR is evidence, never a callable body identity. -/
inductive CoroutineAuxiliaryRole where
  | sync | async | proxyAsync
  deriving Repr, DecidableEq

structure CoroutineSavedField where
  typeId : TypeId
  sourceInfo : SourceInfo
  ignoreForTraits : Bool
  debuginfoName : Option String

structure CoroutineLayoutEvidence where
  fields : Array CoroutineSavedField
  variants : Array (Array Nat)
  variantSources : Array SourceInfo
  storageConflicts : Array (Array Nat)

structure CoroutineEvidence where
  ownerBody : BodyId
  coroutineType : TypeId
  kind : Miri.MIR.CoroutineKind
  yieldType : Option TypeId
  resumeType : Option TypeId
  layout : CoroutineLayoutEvidence
  dropSync : Option Nat
  dropAsync : Option Nat
  dropProxyAsync : Option Nat

structure CoroutineAuxiliaryBody where
  ownerBody : BodyId
  role : CoroutineAuxiliaryRole
  sourceKind : Miri.Interpreter.CallInstanceKind
  /-- `instanceId` in this body records its owner's normalization context. The
  role-qualified auxiliary identity is separate from executable body IDs. -/
  body : Body

structure CoroutineCoverage where
  bodyCoroutines : Array Bool
  coroutines : Array CoroutineEvidence
  auxiliaryBodies : Array CoroutineAuxiliaryBody

end Miri.Input
