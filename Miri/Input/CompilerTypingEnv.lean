import Miri.Input.SourceEnvironment.Material

/-! Pinned rustc ParamEnv/TypingEnv identity. ParamEnv is an ordered clause list;
it has no reveal-mode flag. Source declaration recipes are distinct from derived
query environments, so caller-bound elaboration/normalization is never exported
as an eager query answer. -/
namespace Miri.Input.CompilerTypingEnv
open GenericSubstitution TraitSelection

/-- Local definition lists preserve the pinned interner's order and multiplicity. -/
inductive Mode where
  | coherence
  | typeck (definingOpaqueTypesAndGenerators : Array DefinitionIdentity)
  | postTypeckUntilBorrowck (definingOpaqueTypes : Array DefinitionIdentity)
  | postBorrowck (definedOpaqueTypes : Array DefinitionIdentity)
  | reflection
  | postAnalysis
  | codegen
  | erasedNotCoherence
  deriving Repr, DecidableEq, BEq

structure ParamEnv where
  callerBounds : Array Clause
  deriving Repr, DecidableEq, BEq

structure Env where
  paramEnv : ParamEnv
  mode : Mode
  deriving Repr, DecidableEq, BEq

def fullyMonomorphized : Env := ⟨⟨#[]⟩,.codegen⟩

/-- Reuse canonical source scopes; they include parent/generic-parent identity,
parameters, trait role and own explicit clauses. They are not a ParamEnv. -/
abbrev DeclarationPredicates := SourceEnvironment.Material

inductive Recipe where
  | fullyMonomorphized
  | declaration (owner : DefinitionIdentity) (mode : Mode)
  deriving Repr, DecidableEq

/-- Only the query-free empty Codegen recipe is connected initially. General
recipes must run pinned elaboration/normalization in the current World. -/
def deriveEmpty : Recipe → Except String Env
  | .fullyMonomorphized => .ok fullyMonomorphized
  | .declaration .. => .error "declaration ParamEnv requires on-demand elaboration/normalization"

/-- Provider retry preserves exact caller bounds, even in a Codegen query whose
environment is nonempty. It does not invoke ParamEnv::with_normalized. -/
def postAnalysisRetry (env : Env) : Except String (Option Env) :=
  match env.mode with
  | .codegen => .ok (some {env with mode := .postAnalysis})
  | .coherence | .typeck _ | .postTypeckUntilBorrowck _ | .postBorrowck _
  | .reflection | .postAnalysis => .ok none
  | .erasedNotCoherence => .error "erased typing mode is invalid at a CTFE query provider"

end Miri.Input.CompilerTypingEnv
