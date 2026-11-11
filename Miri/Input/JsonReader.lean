import Lean.Data.Json.Parser
import Std.Data.HashSet

namespace Miri.Input.JsonReader

open Std.Internal.Parsec Std.Internal.Parsec.String

abbrev Parser := Std.Internal.Parsec.String.Parser

def fail (message : String) : Parser α := Std.Internal.Parsec.fail message

def liftExcept (value : Except String α) : Parser α :=
  match value with
  | .ok result => pure result
  | .error error => fail error

def required (value : Option α) (name : String) : Parser α :=
  match value with
  | some result => pure result
  | none => fail s!"missing field `{name}`"

def string : Parser String := skipChar '"' *> Lean.Json.Parser.str

def natural : Parser Nat := do
  match ← Lean.Json.Parser.num with
  | ⟨.ofNat value, 0⟩ => pure value
  | _ => fail "expected unsigned integer"

def integer : Parser Int := do
  let value ← Lean.Json.Parser.num
  if value.exponent == 0 then pure value.mantissa else fail "expected integer"

def boolean : Parser Bool := do
  match ← peek! with
  | 't' => skipString "true"; pure true
  | 'f' => skipString "false"; pure false
  | _ => fail "expected boolean"

def nullable (parser : Parser α) : Parser (Option α) := do
  if (← peek!) == 'n' then skipString "null"; pure none else some <$> parser

private partial def arrayItems (parser : Parser α) (values : Array α) : Parser (Array α) := do
  let value ← parser
  ws
  match ← any with
  | ']' => pure (values.push value)
  | ',' => ws; arrayItems parser (values.push value)
  | _ => fail "expected ',' or ']'"

private partial def indexedItems (parser : Nat → Parser α) (values : Array α) : Parser (Array α) := do
  let value ← parser values.size
  ws
  match ← any with
  | ']' => pure (values.push value)
  | ',' => ws; indexedItems parser (values.push value)
  | _ => fail "expected ',' or ']'"

def arrayIndexed (parser : Nat → Parser α) : Parser (Array α) := do
  skipChar '['; ws
  if (← peek!) == ']' then skip; pure #[] else indexedItems parser #[]

/-- Parse an array with an accumulator local to that array, for checks such as
identity uniqueness against earlier rows. The accumulator is discarded at its end. -/
private partial def stateItems (step : σ → Nat → Parser (α × σ))
    (state : σ) (values : Array α) : Parser (Array α × σ) := do
  let (value, state) ← step state values.size
  ws
  match ← any with
  | ']' => pure (values.push value, state)
  | ',' => ws; stateItems step state (values.push value)
  | _ => fail "expected ',' or ']'"

def arrayWithState (initial : σ) (step : σ → Nat → Parser (α × σ)) : Parser (Array α) := do
  skipChar '['; ws
  if (← peek!) == ']' then skip; pure #[]
  else return (← stateItems step initial #[]).1

def array (parser : Parser α) : Parser (Array α) := do
  skipChar '['; ws
  if (← peek!) == ']' then skip; pure #[] else arrayItems parser #[]

private partial def objectFields (step : σ → String → Parser σ)
    (state : σ) (seen : Std.HashSet String) : Parser σ := do
  let key ← string
  if seen.contains key then fail s!"duplicate field `{key}`"
  ws; skipChar ':'; ws
  let state ← step state key
  ws
  match ← any with
  | '}' => pure state
  | ',' => ws; objectFields step state (seen.insert key)
  | _ => fail "expected ',' or '}'"

/-- A forward-only fold. The accumulator is schema-specific typed data; only
member names are retained to reject duplicate members. -/
def object (initial : σ) (step : σ → String → Parser σ) : Parser σ := do
  skipChar '{'; ws
  if (← peek!) == '}' then skip; pure initial else objectFields step initial {}

private partial def skipStringBody : Parser Unit := do
  let c ← any
  if c == '"' then return
  if c == '\\' then
    let _ ← Lean.Json.Parser.escapedChar
  else if c.toNat < 0x20 then fail "unexpected character in string"
  skipStringBody

mutual
  partial def skipValue : Parser Unit := do
    match ← peek! with
    | '"' => skipChar '"'; skipStringBody
    | '[' =>
      skipChar '['; ws
      if (← peek!) == ']' then skip else skipArray
    | '{' => let _ ← object () (fun _ _ => skipValue); pure ()
    | 't' => skipString "true"
    | 'f' => skipString "false"
    | 'n' => skipString "null"
    | c =>
      if c == '-' || ('0' ≤ c && c ≤ '9') then
        let _ ← Lean.Json.Parser.num
        pure ()
      else fail "unexpected JSON token"

  private partial def skipArray : Parser Unit := do
    skipValue; ws
    match ← any with
    | ']' => pure ()
    | ',' => ws; skipArray
    | _ => fail "expected ',' or ']'"
end

def run (parser : Parser α) (source : String) : Except String α :=
  (do ws; let value ← parser; ws; eof; pure value : Parser α).run source

end Miri.Input.JsonReader
