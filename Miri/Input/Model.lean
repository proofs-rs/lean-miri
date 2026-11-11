import Miri.Input.Model.Types
import Miri.Input.Model.Catalogs

namespace Miri.Input

structure ImportDocument where
  compilerPredicates : Array CompilerPredicateEvidence := #[]
  /-- Version tag for source physical ArgAbi layouts in FnAbi evidence. -/
  compilerAbiLayoutSchema : Option String := none
  producer : Producer
  runtimeTargetDataLayout : Option TargetDataLayoutEvidence := none
  predicates : Array VtablePredicate := #[]
  definitions : Array DefinitionId := #[]
  typeConstants : Array Miri.MIR.TypeConst := #[]
  layouts : Array Layout := #[]
  /-- Exact diagnostic and remapped filenames, shared across all source records. -/
  files : Array String := #[]
  spans : Array SourceSpanData := #[]
  types : Array TypeNode
  allocations : Array AllocationNode
  compilerAllocIdWorld : Option CompilerAllocIdWorld := none
  instances : Array InstanceNode
  selectedScope : Option SelectedScope
  functionAbis : Array FunctionAbi
  bodyRoots : Array BodyRoot := #[]
  bodies : Array Body
  queries : Catalog.Queries
  producerSettings : Catalog.ProducerSettings

structure ExecutionInput where
  document : ImportDocument

end Miri.Input
