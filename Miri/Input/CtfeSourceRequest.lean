import Miri.Input.CtfeMirSource
import Miri.Input.CtfeQueryBridge
import Miri.Input.SourceEnvironment
import Miri.Input.GenericInstantiationWorld

/-! Source-only CTFE frame demand in one compiler universe. Query-root identity
and called-frame identity remain distinct. Preparing a frame grants no compiler
allocation, root-query result, validation or interning capability. -/
namespace Miri.Input.CtfeSourceRequest
open GenericSubstitution
structure Prepared where
  query : CtfeQueryBridge.QueryKey
  frame : InstanceArena.Key
  source : CtfeMirSource.Source
  /-- Instantiated source-explicit clauses, never a normalized ParamEnv. -/
  declarationClauses : Array TraitSelection.Clause

private def verifyInstance (world : TypeArena.World) (key : InstanceArena.Key) : Except String Unit := do
  let verified ← InstanceArena.Key.ofSource world key.kind key.arguments
  unless verified == key do throw "CTFE instance key contradicts its current compiler universe"

/-- Initially only empty Codegen and its exact PostAnalysis retry environment
are connected. General source recipes must be derived in the current World. -/
def prepare (world : TypeArena.World) (environments : SourceEnvironment.Lookup)
    (sources : Array CtfeMirSource.Source) (origin : CompilerTypingEnv.Recipe)
    (query : CtfeQueryBridge.QueryKey) (frame : InstanceArena.Key) (promoted : Option Nat) :
    Except String Prepared := do
  let environment ← CompilerTypingEnv.deriveEmpty origin
  let retry ← CompilerTypingEnv.postAnalysisRetry environment
  unless query.environment == environment || retry == some query.environment do
    throw "CTFE query environment is outside the derived empty-Codegen/retry domain"
  verifyInstance world query.global.callee
  verifyInstance world frame
  let .Item _ := frame.kind | throw "scalar CTFE source policy requires an Item frame"
  let source ← CtfeMirSource.lookup sources frame.definition promoted
  let material ← environments frame.definition
  unless material.parameters == source.parameters do throw "CTFE source generic scope contradicts canonical declaration material"
  let arguments ← GenericInstantiationWorld.ofArguments world 16384 frame.arguments
  let declarationClauses ← SourceEnvironment.instantiate environments 16384 frame.definition arguments
  pure ⟨query,frame,source,declarationClauses⟩
end Miri.Input.CtfeSourceRequest
