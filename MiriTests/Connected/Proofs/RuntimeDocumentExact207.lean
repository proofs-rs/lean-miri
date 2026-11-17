import Miri.Input.RuntimeArrayTypes
import MiriTests.Connected.Proofs.ExactMap212
import MiriTests.Connected.Proofs.CompilerPatternDecEq219
import MiriTests.Connected.Proofs.SourceTraitPatternEquality

/-! Structural equality for decoded compiler inputs includes the final MIR,
compiler catalogs, allocation identities and source metadata. No diagnostic
JSON representation participates in this decision procedure. -/
namespace Miri.Verification.RuntimeDocumentExact207

open Miri.Input

local instance : DecidableEq CompilerPattern :=
  PatternEquality219.compilerPatternDecEqInstance

deriving instance DecidableEq for TaggedNode
deriving instance DecidableEq for FieldShape
deriving instance DecidableEq for PrimitiveLayout
deriving instance DecidableEq for ScalarLayout
deriving instance DecidableEq for BackendRepr
deriving instance DecidableEq for NicheLayout
deriving instance DecidableEq for LayoutVariant
deriving instance DecidableEq for TagEncoding
deriving instance DecidableEq for VariantsLayout
deriving instance DecidableEq for Layout
deriving instance DecidableEq for FunctionSignature
deriving instance DecidableEq for DiscriminantValue
deriving instance DecidableEq for DiscriminantInfo
deriving instance DecidableEq for TypeShape
deriving instance DecidableEq for SourceSimd
deriving instance DecidableEq for SourceCoroutineLayout
deriving instance DecidableEq for SourceTypeLayout
deriving instance DecidableEq for TypeNode
deriving instance DecidableEq for FunctionAllocation
deriving instance DecidableEq for StaticGlobalInfo
deriving instance DecidableEq for StaticAllocation
deriving instance DecidableEq for VtablePredicate
deriving instance DecidableEq for VtableEntry
deriving instance DecidableEq for VtableAllocation
deriving instance DecidableEq for AllocationData
deriving instance DecidableEq for AllocationNode
deriving instance DecidableEq for CallResolutionEvidence
deriving instance DecidableEq for LocalDecl
deriving instance DecidableEq for ThreadLocalEvidence
deriving instance DecidableEq for PlaceFact
deriving instance DecidableEq for NodeFacts
deriving instance DecidableEq for BodyCore
deriving instance DecidableEq for PromotedBody
deriving instance DecidableEq for Body
deriving instance DecidableEq for BodyRoot
deriving instance DecidableEq for InstanceNode
deriving instance DecidableEq for SelectedScope
deriving instance DecidableEq for CompilerPredicateEvidence
deriving instance DecidableEq for Catalog.ThreadLocal
deriving instance DecidableEq for Catalog.Queries
deriving instance DecidableEq for CoroutineSavedField
deriving instance DecidableEq for CoroutineLayoutEvidence
deriving instance DecidableEq for CoroutineEvidence
deriving instance DecidableEq for CoroutineAuxiliaryBody
deriving instance DecidableEq for CoroutineCoverage
deriving instance DecidableEq for SourceAbiPolicy
deriving instance DecidableEq for SourceAbiDefinition
deriving instance DecidableEq for SourceAbiMaterial
local instance : DecidableEq SourceTraitPattern := SourceTraitPatternEquality.patternDecEq
deriving instance DecidableEq for SourceTraitType
deriving instance DecidableEq for SourceTraitMaterial
deriving instance DecidableEq for ImportDocument
private theorem runtimeMetadata_eq (left right : RuntimeMetadata)
    (source : left.source = right.source) (target : left.target = right.target) :
    left = right := by
  cases left with
  | mk leftSource leftTarget leftQuery leftQuery_eq =>
    cases right with
    | mk rightSource rightTarget rightQuery rightQuery_eq =>
      cases source
      cases target
      have queries : leftQuery = rightQuery :=
        funext fun id => (leftQuery_eq id).trans (rightQuery_eq id).symm
      cases queries
      rfl

def runtimeMetadataDecidableEq (documentEq : DecidableEq ImportDocument) :
    DecidableEq RuntimeMetadata := by
  letI := documentEq
  exact fun left right =>
  if source : left.source = right.source then
    if target : left.target = right.target then
      isTrue (runtimeMetadata_eq left right source target)
    else isFalse fun equal => target (congrArg RuntimeMetadata.target equal)
  else isFalse fun equal => source (congrArg RuntimeMetadata.source equal)
instance : DecidableEq RuntimeMetadata := runtimeMetadataDecidableEq inferInstance

deriving instance DecidableEq for RuntimeArrayTypes.Entry
deriving instance DecidableEq for RuntimeArrayTypes.World

def documentDecidableEq : DecidableEq ImportDocument := inferInstance

theorem documentDecidableEq_reflect (left right : ImportDocument) :
    (documentDecidableEq left right).decide = true ↔ left = right := by
  cases documentDecidableEq left right with
  | isTrue equal => simp [equal]
  | isFalse different => simp [different]

#print axioms documentDecidableEq
#print axioms documentDecidableEq_reflect

end Miri.Verification.RuntimeDocumentExact207
