import Miri.Input.Model.Types

/-! Finite foreign-symbol declaration material. No symbol winner, numeric
instance identity, function ABI, or executable body is stored here. -/
namespace Miri.Input.SourceSymbols

inductive ParameterKind where
  | region | typeParameter | constParameter
  deriving Repr, DecidableEq

structure Attributes where
  symbolName : Option String
  itemName : Option String
  noMangle : Bool
  stdInternalSymbol : Bool
  linkage : Option String
  procMacroDeclarations : Bool
  deriving Repr, DecidableEq

structure Span where
  isDummy : Bool
  lo : Nat
  hi : Nat
  context : String
  parentLocalDefinition : Option Nat
  file : String
  startLine : Nat
  startColumn : Nat
  endLine : Nat
  endColumn : Nat
  deriving Repr, DecidableEq

structure Declaration where
  iterationIndex : Nat
  used : Bool
  definition : DefinitionId
  path : String
  /-- Source classification: function, associated_function, static, or other. -/
  kind : String
  /-- Traversal provenance can differ from the definition's owning crate. -/
  crateIndex : Nat
  crateName : String
  compilerBuiltins : Bool
  attributes : Attributes
  span : Span
  /-- Complete original slots, flattened after checking the lexical chain. -/
  parameters : Array ParameterKind
  deriving Repr, DecidableEq

structure Material where
  internalSymbolNamespace : String
  declarations : Array Declaration
  deriving Repr, DecidableEq

end Miri.Input.SourceSymbols
