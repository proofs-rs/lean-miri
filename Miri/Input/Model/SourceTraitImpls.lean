import Miri.Input.Model.SourceAbi
/-! Finite trait declarations and manual impl headers, not selection answers.
Missing detailed syntax for a rigid header permits only proven disjointness. -/
namespace Miri.Input.SourceTraitImpls
structure Syntax where
  parameters : Array SourceSymbols.ParameterKind
  selfType : SourceTypes.TypeRef
  traitArguments : Array SourceTypes.TypeRef
  clauses : Array SourceAbi.Clause
  nonConst : Bool
  isFinal : Bool
  deriving Repr, DecidableEq
inductive Polarity where
  | positive | negative | reservation
  deriving Repr, DecidableEq
structure Implementation where
  definition : DefinitionId
  outerHead : SourceAbi.AutoSelfHead
  polarity : Polarity
  header : Option Syntax
  deriving Repr, DecidableEq
structure Declaration where
  definition : DefinitionId
  isAuto : Bool
  hasSelf : Bool
  parameters : Array SourceSymbols.ParameterKind
  associatedItems : Nat
  superClauses : Array SourceAbi.Clause
  implementations : Array Implementation
  deriving Repr, DecidableEq
structure Material where
  declarations : Array Declaration
  deriving Repr, DecidableEq
end Miri.Input.SourceTraitImpls
