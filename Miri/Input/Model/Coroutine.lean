import Miri.Input.Model.Types
import Miri.Input.CoroutineBodyDispatch

namespace Miri.Input

/-- Compiler-owned auxiliary MIR is evidence, never a callable body identity. -/
inductive CoroutineAuxiliaryRole where
  | sync | async | proxyAsync
  deriving Repr, DecidableEq

structure CoroutineSavedField (Child : Type := TypeId) where
  typeId : Child
  sourceInfo : SourceInfo
  ignoreForTraits : Bool
  debuginfoName : Option String
  deriving DecidableEq

structure CoroutineLayoutEvidence (Child : Type := TypeId) where
  fields : Array (CoroutineSavedField Child)
  variants : Array (Array Nat)
  variantSources : Array SourceInfo
  storageConflicts : Array (Array Nat)
  deriving DecidableEq

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

/-- Raw generic declaration selected by a physical MIR owner. Layout evidence
contains source field terms and raw relations, never physical layout answers. -/
structure CoroutineGenericSource where
  owner : GenericSubstitution.DefinitionIdentity
  physicalOwner : GenericSubstitution.DefinitionIdentity
  typeckOwner : GenericSubstitution.DefinitionIdentity
  parentCount : Nat
  parameters : Array GenericSubstitution.ArgSort
  witnessParameters : Array GenericSubstitution.ArgSort
  typeExpression : GenericSubstitution.Term
  identityKind : GenericSubstitution.Term
  byMoveOwner : Option GenericSubstitution.DefinitionIdentity
  layout : CoroutineLayoutEvidence GenericSubstitution.Term
  deriving DecidableEq

structure CoroutineCoverage where
  bodyCoroutines : Array Bool
  coroutines : Array CoroutineEvidence
  auxiliaryBodies : Array CoroutineAuxiliaryBody
  genericSources : Array CoroutineGenericSource := #[]

end Miri.Input
