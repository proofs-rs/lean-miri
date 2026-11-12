import Miri.MIR.Syntax

/-! Raw pinned rustc representation attributes shared by source declarations
and material type shapes. These are declaration syntax and session seed inputs,
not computed field offsets, scalar ranges or physical layout answers. -/
namespace Miri.Input

inductive IntegerTypeTag where
  | known (kind : Miri.MIR.IntegerKind)
  deriving Repr, DecidableEq

inductive ReprInteger where
  | pointerSized (signed : Bool)
  | fixed (kind : IntegerTypeTag) (sizeBits : Nat) (signed : Bool)
  deriving Repr, DecidableEq

inductive ScalableElement where
  | elementCount (count : Nat)
  | container
  deriving Repr, DecidableEq

structure ReprOptions where
  integer : Option ReprInteger
  alignBytes : Option Nat
  packBytes : Option Nat
  flagsBits : Nat
  scalableElement : Option ScalableElement
  fieldShuffleSeed : Nat
  deriving Repr, DecidableEq

namespace ReprOptions

-- Pinned rustc_abi::ReprOptions keeps these properties in flags, int and pack.
def c (repr : ReprOptions) : Bool := repr.flagsBits &&& 1 != 0
def simd (repr : ReprOptions) : Bool := repr.flagsBits &&& 2 != 0
def transparent (repr : ReprOptions) : Bool := repr.flagsBits &&& 4 != 0
def linear (repr : ReprOptions) : Bool := repr.flagsBits &&& 8 != 0
def scalable (repr : ReprOptions) : Bool := repr.flagsBits &&& 64 != 0
def rust (repr : ReprOptions) : Bool := !repr.c && !repr.simd && !repr.scalable && !repr.transparent
def packed (repr : ReprOptions) : Bool := repr.packBytes.isSome
def inhibitEnumLayoutOptimization (repr : ReprOptions) : Bool := repr.c || repr.integer.isSome
def inhibitNewtypeAbiOptimization (repr : ReprOptions) : Bool := repr.c || repr.simd
def inhibitStructFieldReordering (repr : ReprOptions) : Bool :=
  repr.c || repr.simd || repr.scalable || repr.linear || repr.integer.isSome
def canRandomizeTypeLayout (repr : ReprOptions) : Bool :=
  !repr.inhibitStructFieldReordering && repr.flagsBits &&& 16 != 0

end ReprOptions

end Miri.Input
