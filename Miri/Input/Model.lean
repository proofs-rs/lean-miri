import Miri.Input.CompilerTables
import Miri.Input.DecoderValues

namespace Miri.Input

structure ImportDocumentCore where
  compilerPredicates : Array CompilerPredicateEvidence := #[]
  /-- Version tag for source physical ArgAbi layouts in FnAbi evidence. -/
  compilerAbiLayoutSchema : Option String := none
  producer : Producer
  runtimeTargetDataLayout : Option TargetDataLayoutEvidence := none
  completenessStatus : PayloadStatus
  types : Array TypeNode
  layoutTable : Miri.MIR.SharedTable Layout := #[]
  projectionTables : ProjectionTables := {}
  typeRelationTables : TypeRelationTables := {}
  compilerFactTables : CompilerFactTables := {}
  compilerTypeCatalogs : CompilerTypeCatalogs := {}
  abiTables : AbiTables := {}
  abiQueries : AbiQueries := {}
  covarianceQueries : Except String (Array CovarianceQuery) := .error "covariance queries absent"
  vtableTables : VtableTables := {}
  mirTables : MIRInputTables := {}
  allocations : Array AllocationNode
  compilerAllocIdWorld : Option CompilerAllocIdWorld := none
  instances : Array InstanceNode
  selectedScope : Option SelectedScope
  bodies : Array Body
  sourceSpans : Miri.MIR.SharedTable SourceSpanData := #[]
  rootSpan : Option Nat := none
  rootSpanDeclared : Bool := false
  validatedVtableProbeDiagnostics : Array String := #[]
  obligations : Array Obligation
  raw : Lean.Json
  /-- Original transport nodes. Children retain the producer's shared IDs. -/
  sharedNodes : Array Lean.Json := #[]
  compilerValueMemo : Option CompilerValueMemo := none

def ImportDocumentCore.instance (document : ImportDocumentCore) (id : InstanceId) : Except String InstanceNode := do
  let some value := document.instances[id]? | throw s!"invalid instance ID {id}"
  return value

/-- Full diagnostic import retained for callers that inspect the typed JSON
projection. Runtime decoding uses `ImportDocumentCore` and does not retain this
duplicate tree. -/
structure ImportDocument where
  compilerPredicates : Array CompilerPredicateEvidence := #[]
  /-- Version tag for source physical ArgAbi layouts in FnAbi evidence. -/
  compilerAbiLayoutSchema : Option String := none
  producer : Producer
  runtimeTargetDataLayout : Option TargetDataLayoutEvidence := none
  completenessStatus : PayloadStatus
  types : Array TypeNode
  layoutTable : Miri.MIR.SharedTable Layout := #[]
  projectionTables : ProjectionTables := {}
  typeRelationTables : TypeRelationTables := {}
  compilerFactTables : CompilerFactTables := {}
  compilerTypeCatalogs : CompilerTypeCatalogs := {}
  abiTables : AbiTables := {}
  abiQueries : AbiQueries := {}
  covarianceQueries : Except String (Array CovarianceQuery) := .error "covariance queries absent"
  vtableTables : VtableTables := {}
  mirTables : MIRInputTables := {}
  allocations : Array AllocationNode
  compilerAllocIdWorld : Option CompilerAllocIdWorld := none
  instances : Array InstanceNode
  selectedScope : Option SelectedScope
  bodies : Array Body
  sourceSpans : Miri.MIR.SharedTable SourceSpanData := #[]
  rootSpan : Option Nat := none
  rootSpanDeclared : Bool := false
  typedTree : TypedValue
  validatedVtableProbeDiagnostics : Array String := #[]
  obligations : Array Obligation
  raw : Lean.Json
  /-- Original transport nodes; references are not expanded. -/
  sharedNodes : Array Lean.Json := #[]

/-- Diagnostic/reflected imports contain schema data only. Their runtime view
uses the uncached compatibility path; the native runtime importer retains the
checked compiler projections directly in ImportDocumentCore. -/
def ImportDocument.toCore (document : ImportDocument) : ImportDocumentCore := {
  compilerPredicates := document.compilerPredicates
  compilerAbiLayoutSchema := document.compilerAbiLayoutSchema
  producer := document.producer
  runtimeTargetDataLayout := document.runtimeTargetDataLayout
  completenessStatus := document.completenessStatus
  types := document.types
  layoutTable := document.layoutTable
  projectionTables := document.projectionTables
  typeRelationTables := document.typeRelationTables
  compilerFactTables := document.compilerFactTables
  compilerTypeCatalogs := document.compilerTypeCatalogs
  abiTables := document.abiTables
  abiQueries := document.abiQueries
  covarianceQueries := document.covarianceQueries
  vtableTables := document.vtableTables
  mirTables := document.mirTables
  allocations := document.allocations
  compilerAllocIdWorld := document.compilerAllocIdWorld
  instances := document.instances
  selectedScope := document.selectedScope
  bodies := document.bodies
  sourceSpans := document.sourceSpans
  rootSpan := document.rootSpan
  rootSpanDeclared := document.rootSpanDeclared
  validatedVtableProbeDiagnostics := document.validatedVtableProbeDiagnostics
  obligations := document.obligations
  raw := document.raw
  sharedNodes := document.sharedNodes
}

/-- Diagnostic clients may pass their full document to core-only consumers
without retaining the generic tree in the resulting runtime metadata. -/
instance : Coe ImportDocument ImportDocumentCore := ⟨ImportDocument.toCore⟩

def ImportDocumentCore.withTypedTree (core : ImportDocumentCore) (typedTree : TypedValue) : ImportDocument := {
  compilerPredicates := core.compilerPredicates
  compilerAbiLayoutSchema := core.compilerAbiLayoutSchema
  producer := core.producer
  runtimeTargetDataLayout := core.runtimeTargetDataLayout
  completenessStatus := core.completenessStatus
  types := core.types
  layoutTable := core.layoutTable
  projectionTables := core.projectionTables
  typeRelationTables := core.typeRelationTables
  compilerFactTables := core.compilerFactTables
  compilerTypeCatalogs := core.compilerTypeCatalogs
  abiTables := core.abiTables
  abiQueries := core.abiQueries
  covarianceQueries := core.covarianceQueries
  vtableTables := core.vtableTables
  mirTables := core.mirTables
  allocations := core.allocations
  compilerAllocIdWorld := core.compilerAllocIdWorld
  instances := core.instances
  selectedScope := core.selectedScope
  bodies := core.bodies
  sourceSpans := core.sourceSpans
  rootSpan := core.rootSpan
  rootSpanDeclared := core.rootSpanDeclared
  typedTree := typedTree
  validatedVtableProbeDiagnostics := core.validatedVtableProbeDiagnostics
  obligations := core.obligations
  raw := core.raw
  sharedNodes := core.sharedNodes
}

/-- A structurally complete input accepted by the decoder.  This is still not
a semantic model or a proof of Miri equivalence. -/
structure ExecutionInput where
  document : ImportDocument

structure RuntimeExecutionInput where
  document : ImportDocumentCore

structure DecodeResult where
  document : ImportDocument
  executionInput : Option ExecutionInput
  /-- Exact obligations that make `executionInput` unavailable under the
  decoder's existing readiness predicate. This is diagnostic evidence only;
  it does not relax or otherwise define execution readiness. -/
  blockingObligations : Array Obligation := #[]

structure RuntimeDecodeResult where
  document : ImportDocumentCore
  executionInput : Option RuntimeExecutionInput
  blockingObligations : Array Obligation := #[]

end Miri.Input
