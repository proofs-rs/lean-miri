import Miri.Interpreter.ForeignItems
import Miri.Interpreter.ExternStatic

namespace Miri.Input
set_option autoImplicit false
open Miri.Interpreter Miri.ABI Miri.Memory

structure ForeignSymbolCandidate where
  symbol : String
  explicitSymbol : Bool
  /-- Only callable exports need a MIR instance. Statics/non-callables must
  still participate in symbol clashes and in the exported-function UB guard. -/
  fnInstance : Option CallInstance
  crateIndex : Nat
  crateName : String
  weak : Bool
  spanLo : Nat
  spanHi : Nat
  kind : ForeignItems.ExportKind
  compilerBuiltins : Bool
  deriving Repr, DecidableEq

inductive ForeignAllocatorTarget where
  | redirect (symbol : String)
  | special (method : ForeignItems.SpecialAllocatorMethod)
  deriving Repr, DecidableEq

structure ForeignAllocatorEntry where
  symbol : String
  target : ForeignAllocatorTarget
  deriving Repr, DecidableEq

structure ForeignSymbolsData where
  noAllocShimSymbol : String
  /-- Exact `iter_exported_symbols` iteration order; do not sort this array. -/
  candidates : Array ForeignSymbolCandidate
  allocatorEntries : Array ForeignAllocatorEntry
  deriving Repr, DecidableEq

structure ExternStaticDeclarationData where
  definition : MIR.DefId
  symbol : String
  size : Size
  align : Align
  linkage : ExternStatic.ImportLinkage
  mutable : Bool
  result : Except String Unit
  deriving DecidableEq, Repr

structure ExternStaticWinnerData where
  definition : Option MIR.DefId
  kind : String
  allocation : Option MIR.AllocationId
  status : String
  reason : String
  deriving DecidableEq, Repr

structure ExternStaticSelectedData where
  symbol : String
  winner : ExternStaticWinnerData
  deriving DecidableEq, Repr

/-- Target attributes returned by rustc's parsed Session target. `families`
is the exact cfg family set; neither family nor environment is inferred from
the target triple. -/
structure CompilerTargetFactsData where
  os : String
  env : String
  binaryFormat : String
  families : Array String
  deriving DecidableEq, Repr

structure ExternStaticsData where
  sourceStatus : Except String Unit
  targetFacts : Except String CompilerTargetFactsData
  declarations : Array ExternStaticDeclarationData
  selected : Array ExternStaticSelectedData
  deriving Repr, DecidableEq

end Miri.Input
