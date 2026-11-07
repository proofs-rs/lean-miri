import Miri.ABI.FnAbi

namespace Miri.Interpreter.ForeignItems
open Miri.ABI

inductive SignatureType where
  | unit | usize | isize | i32 | u32 | pointer | unitPointer | alignment | never
  | u64 | u8 | bool | byteSlice | functionPointer
  deriving DecidableEq, Repr

structure Signature where
  conv : CanonAbi
  args : Array SignatureType
  ret : SignatureType
  deriving DecidableEq, Repr

end Miri.Interpreter.ForeignItems
