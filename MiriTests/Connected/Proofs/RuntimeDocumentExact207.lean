import Miri.Input.RuntimeArrayTypes
import MiriTests.Connected.Proofs.ExactMap212
import MiriTests.Connected.Proofs.CompilerPatternDecEq219

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
deriving instance DecidableEq for CanonicalAbi
deriving instance DecidableEq for FunctionSignature
deriving instance DecidableEq for AdtCompilerFacts
deriving instance DecidableEq for ProjectionField
deriving instance DecidableEq for ProjectionParent
deriving instance DecidableEq for ProjectionQueries
deriving instance DecidableEq for DiscriminantValue
deriving instance DecidableEq for DiscriminantInfo
deriving instance DecidableEq for TypeCompilerFacts
deriving instance DecidableEq for TypeShape
deriving instance DecidableEq for TypeNode
deriving instance DecidableEq for AbiAttributes
deriving instance DecidableEq for AbiRegisterHint
deriving instance DecidableEq for AbiRegister
deriving instance DecidableEq for AbiCastTarget
deriving instance DecidableEq for AbiPassMode
deriving instance DecidableEq for AbiArgument
deriving instance DecidableEq for FunctionAbi
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
deriving instance DecidableEq for DynamicUpcastEvidence
deriving instance DecidableEq for NodeFacts
deriving instance DecidableEq for BodyCore
deriving instance DecidableEq for PromotedBody
deriving instance DecidableEq for Body
deriving instance DecidableEq for BodyRoot
deriving instance DecidableEq for InstanceNode
deriving instance DecidableEq for SelectedScope
deriving instance DecidableEq for CompilerPredicateEvidence
deriving instance DecidableEq for Catalog.VtableQuery
deriving instance DecidableEq for Catalog.ThreadLocal
deriving instance DecidableEq for Catalog.Queries
deriving instance DecidableEq for CoroutineSavedField
deriving instance DecidableEq for CoroutineLayoutEvidence
deriving instance DecidableEq for CoroutineEvidence
deriving instance DecidableEq for CoroutineAuxiliaryBody
deriving instance DecidableEq for CoroutineCoverage
deriving instance DecidableEq for ImportDocument
deriving instance DecidableEq for RuntimeMetadata
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
