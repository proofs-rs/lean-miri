import Miri.Input.CtfeMirSource
import Miri.Input.TraitSelection.Material
import Miri.Input.Model.Types
import Miri.Input.Model.Catalogs
import Miri.Input.Model.Coroutine

namespace Miri.Input

structure CompilerTypeConstResult where
  aliasKind : String
  rigid : Bool
  definition : Nat
  genericArgs : Array Miri.MIR.GenericArg
  valueConstId : TypeConstantId
  deriving BEq

structure ImportDocument where
  traitProgram : TraitSelection.Program := {traits := #[]}
  compilerPredicates : Array CompilerPredicateEvidence := #[]
  /-- Version tag for source physical ArgAbi layouts in FnAbi evidence. -/
  compilerAbiLayoutSchema : Option String := none
  producer : Producer
  runtimeTargetDataLayout : Option TargetDataLayoutEvidence := none
  predicates : Array VtablePredicate := #[]
  definitions : Array DefinitionId := #[]
  typeConstants : Array Miri.MIR.TypeConst := #[]
  /-- rustc-evaluated answers for concrete type-level alias demands. -/
  compilerTypeConstResults : Array CompilerTypeConstResult := #[]
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
  mirTemplates : Array CopyTemplateSource := #[]
  /-- Bounded raw CTFE frame sources; absence never grants query admission. -/
  ctfeScalarSources : Array CtfeMirSource.Source := #[]
  bodies : Array BodySeed
  coroutineCoverage : Option CoroutineCoverage := none
  queries : Catalog.Queries
  producerSettings : Catalog.ProducerSettings

structure ExecutionInput where
  document : ImportDocument

end Miri.Input
