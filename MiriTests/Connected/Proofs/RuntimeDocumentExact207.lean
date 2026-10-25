import Miri.Input.RuntimeArrayTypes
import MiriTests.Connected.Proofs.ExactMap212
import MiriTests.Connected.Proofs.TypedValueDecidableEq207

/-! Conditional input-model closure for exact state equality. The only external
assumption is a computable, kernel-checked `DecidableEq Lean.Json`; JSON's
existing `BEq` is deliberately not used. Once Json213 exports that instance,
all derived instances below specialize to it. -/
namespace Miri.Verification.RuntimeDocumentExact207

section
variable [DecidableEq Lean.Json] [DecidableEq CompilerPattern]

open Miri.Input

deriving instance DecidableEq for UserTypeProjection
deriving instance DecidableEq for TaggedNode

local instance : DecidableEq TypedValue :=
  TypedValueDecEq207.typedValueDecidableEq

deriving instance DecidableEq for FieldShape
deriving instance DecidableEq for PrimitiveLayout
deriving instance DecidableEq for ScalarLayout
deriving instance DecidableEq for BackendRepr
deriving instance DecidableEq for LayoutVariant
deriving instance DecidableEq for TagEncoding
deriving instance DecidableEq for VariantsLayout
deriving instance DecidableEq for Layout
deriving instance DecidableEq for ExternAbi
deriving instance DecidableEq for CanonicalAbi
deriving instance DecidableEq for FunctionSignature
deriving instance DecidableEq for CompilerBooleanEvidence
deriving instance DecidableEq for CompilerTypeEvidence
deriving instance DecidableEq for TypeCompilerFacts
deriving instance DecidableEq for TypeNode

deriving instance DecidableEq for AbiAttributes
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

deriving instance DecidableEq for MirNode
deriving instance DecidableEq for BasicBlock
deriving instance DecidableEq for LocalDecl
deriving instance DecidableEq for BodyCore
deriving instance DecidableEq for PromotedBody
deriving instance DecidableEq for Body
deriving instance DecidableEq for InstanceNode
deriving instance DecidableEq for SelectedScope
deriving instance DecidableEq for TargetDataLayoutEvidence
deriving instance DecidableEq for CompilerPredicateEvidence
-- Cache equality includes exact stored entries; proof fields use proof
-- irrelevance, just like the existing source-bound runtime caches below.
deriving instance DecidableEq for DecoderValues.CompilerFunctionAbiTable
deriving instance DecidableEq for DecoderValues.CompilerValueMemo
deriving instance DecidableEq for ImportDocumentCore
deriving instance DecidableEq for ImportDocument

deriving instance DecidableEq for RuntimeNodeLookupCache
deriving instance DecidableEq for RuntimeLayoutLookupCache
deriving instance DecidableEq for RuntimeMetadata
deriving instance DecidableEq for RuntimeArrayTypes.Entry
deriving instance DecidableEq for RuntimeArrayTypes.World

#print axioms TypedValueDecEq207.typedValueDecidableEq
#print axioms TypedValueDecEq207.typedValueDecEq_reflect

end

end Miri.Verification.RuntimeDocumentExact207
