import Lean
namespace Miri.Interpreter.CompileTime.Counter
inductive Event where
  | none | lint (isError : Bool) | progressWarning (uniqueStep : Nat)
  deriving Repr, DecidableEq, BEq
structure Config where
  /-- Compiler host usize width, not guest target pointer width. -/
  hostBits : Nat
  tinyLimit : Bool
  lintIsError : Bool
structure Step where
  count : Nat
  event : Event
  stopAsReported : Bool
  deriving Repr, DecidableEq, BEq

def increment (config : Config) (count : Nat) : Except String Step := do
  unless config.hostBits > 0 && count < 2^config.hostBits do
    throw "invalid compiler-host usize counter"
  if count + 1 == 2^config.hostBits then return ⟨count,.none,false⟩
  let next := count + 1
  let limit := if config.tinyLimit then 20 else 2000000
  let start := if config.tinyLimit then 20 else 4000000
  if next == limit then
    return ⟨next,.lint config.lintIsError,config.lintIsError⟩
  if next > start && next &&& (next-1) == 0 then
    return ⟨next,.progressWarning next,false⟩
  return ⟨next,.none,false⟩

end Miri.Interpreter.CompileTime.Counter
