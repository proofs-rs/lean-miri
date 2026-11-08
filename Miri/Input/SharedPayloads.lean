import Miri.Input.SemanticTables

/-! Numeric semantic tables are retained as input. This module validates the
catalog boundary; schema decoders demand individual nodes in their own kinds.
It deliberately performs no JSON expansion. -/
namespace Miri.Input.SharedPayloads
open Lean

structure ResolvedGraph where
  nodes : Array Json
  root : Json
  nodeResolutionCount : Nat
  semanticTables : SemanticTables.Catalog := SemanticTables.empty
  deriving Inhabited

def resolveGraph (document : Json) : Except String ResolvedGraph := do
  let catalog ← SemanticTables.parse document
  if (document.getObjVal? "shared_payloads").isOk then
    throw "$.shared_payloads: obsolete transport graph; expected numeric semantic tables"
  let nodes := SemanticTables.kinds.foldl (fun out kind => out ++ catalog.nodes kind) #[]
  return { nodes, root := document, nodeResolutionCount := 0, semanticTables := catalog }

def resolveCatalog (document : Json) : Except String Json := do
  return (← resolveGraph document).root

end Miri.Input.SharedPayloads
