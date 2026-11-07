import Lean

namespace Miri.Input

inductive RuntimeMetadataError where
  | missing (path : String)
  | unsupported (path : String)
  | invalid (path message : String)
  | duplicateType (id : Nat)
  | unknownType (id : Nat)
  deriving DecidableEq, Repr
instance : ToString RuntimeMetadataError where
  toString e := reprStr e


end Miri.Input
