import Miri.Input.Model.Types
import Miri.Input.Model.Catalogs
import Miri.Input.Model.Coroutine
import Miri.Input.Model.SourceMaterial

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
  coroutineCoverage : Option CoroutineCoverage := none
  queries : Catalog.Queries
  producerSettings : Catalog.ProducerSettings
  /-- Original finite typed source facts, distinct from imported query answers.
  None is the legacy metadata path; Some forbids pretending absent source MIR
  or ABI material was supplied by an existing unrelated catalog row. -/
  sourceMaterial : Option SourceMaterial := none

structure ExecutionInput where
  document : ImportDocument

end Miri.Input
