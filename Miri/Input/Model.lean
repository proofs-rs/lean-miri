import Miri.Input.DecoderValues

namespace Miri.Input

structure ImportDocumentCore where
  compilerPredicates : Array CompilerPredicateEvidence := #[]
  /-- Version tag for source physical ArgAbi layouts in FnAbi evidence. -/
  compilerAbiLayoutSchema : Option String := none
  producer : Producer
  runtimeTargetDataLayout : Option TargetDataLayoutEvidence := none
  types : Array TypeNode
  allocations : Array AllocationNode
  compilerAllocIdWorld : Option CompilerAllocIdWorld := none
  instances : Array InstanceNode
  selectedScope : Option SelectedScope
  functionAbis : Array FunctionAbi
  bodies : Array Body
  raw : Lean.Json
  /-- Resolved source nodes from the mandatory shared-payload graph. Each node
  is retained once so downstream consumers can reuse the document's DAG. -/
  sharedNodes : Array Lean.Json := #[]
  semanticTables : SemanticTables.Catalog := SemanticTables.empty
  /-- Checked import-time ABI projections indexed by their exact source JSON. -/
  compilerFunctionAbiTable : Option (CompilerFunctionAbiTable sharedNodes) := none
  compilerValueMemo : Option CompilerValueMemo := none

/-- Full diagnostic import retained for callers that inspect the typed JSON
projection. Runtime decoding uses `ImportDocumentCore` and does not retain this
duplicate tree. -/
structure ImportDocument where
  compilerPredicates : Array CompilerPredicateEvidence := #[]
  /-- Version tag for source physical ArgAbi layouts in FnAbi evidence. -/
  compilerAbiLayoutSchema : Option String := none
  producer : Producer
  runtimeTargetDataLayout : Option TargetDataLayoutEvidence := none
  types : Array TypeNode
  allocations : Array AllocationNode
  compilerAllocIdWorld : Option CompilerAllocIdWorld := none
  instances : Array InstanceNode
  selectedScope : Option SelectedScope
  functionAbis : Array FunctionAbi
  bodies : Array Body
  typedTree : TypedValue
  raw : Lean.Json
  /-- Resolved source nodes from the mandatory shared-payload graph. -/
  sharedNodes : Array Lean.Json := #[]
  semanticTables : SemanticTables.Catalog := SemanticTables.empty

/-- Diagnostic/reflected imports contain schema data only. Their runtime view
uses the uncached metadata path; the native runtime importer retains the
checked compiler projections directly in ImportDocumentCore. -/
def ImportDocument.toCore (document : ImportDocument) : ImportDocumentCore := {
  compilerPredicates := document.compilerPredicates
  compilerAbiLayoutSchema := document.compilerAbiLayoutSchema
  producer := document.producer
  runtimeTargetDataLayout := document.runtimeTargetDataLayout
  types := document.types
  allocations := document.allocations
  compilerAllocIdWorld := document.compilerAllocIdWorld
  instances := document.instances
  selectedScope := document.selectedScope
  functionAbis := document.functionAbis
  bodies := document.bodies
  raw := document.raw
  sharedNodes := document.sharedNodes
  semanticTables := document.semanticTables
}

/-- Diagnostic clients may pass their full document to core-only consumers
without retaining the generic tree in the resulting runtime metadata. -/
instance : Coe ImportDocument ImportDocumentCore := ⟨ImportDocument.toCore⟩

def ImportDocumentCore.withTypedTree (core : ImportDocumentCore) (typedTree : TypedValue) : ImportDocument := {
  compilerPredicates := core.compilerPredicates
  compilerAbiLayoutSchema := core.compilerAbiLayoutSchema
  producer := core.producer
  runtimeTargetDataLayout := core.runtimeTargetDataLayout
  types := core.types
  allocations := core.allocations
  compilerAllocIdWorld := core.compilerAllocIdWorld
  instances := core.instances
  selectedScope := core.selectedScope
  functionAbis := core.functionAbis
  bodies := core.bodies
  typedTree := typedTree
  raw := core.raw
  sharedNodes := core.sharedNodes
  semanticTables := core.semanticTables
}

/-- A structurally complete input accepted by the decoder.  This is still not
a semantic model or a proof of Miri equivalence. -/
structure ExecutionInput where
  document : ImportDocument

structure RuntimeExecutionInput where
  document : ImportDocumentCore

structure DecodeResult where
  document : ImportDocument
  executionInput : ExecutionInput

structure RuntimeDecodeResult where
  document : ImportDocumentCore
  executionInput : RuntimeExecutionInput

end Miri.Input
