import Lean.Data.Json.Parser

namespace Miri.Input.JsonReader

open Std.Internal.Parsec Std.Internal.Parsec.String

/-- A borrowed JSON token. Only the source string and its byte positions are retained. -/
structure Slice where
  private start : Sigma String.Pos
  private stop : String.Pos.Raw

def Slice.text (value : Slice) : String :=
  String.Pos.Raw.extract value.start.1 value.start.2.offset value.stop

private def position : Parser (Sigma String.Pos) := fun it => .success it it

private partial def skipStringBody : Parser Unit := do
  let c ← any
  if c == '"' then return
  if c == '\\' then
    let _ ← Lean.Json.Parser.escapedChar
  else if c.toNat < 0x20 then
    fail "unexpected character in string"
  skipStringBody

private def skipStringToken : Parser Unit := skipChar '"' *> skipStringBody

mutual
  private partial def skipValue : Parser Unit := do
    match ← peek! with
    | '"' => skipStringToken
    | '[' =>
      skip; ws
      if (← peek!) == ']' then skip else skipArray
    | '{' =>
      skip; ws
      if (← peek!) == '}' then skip else skipObject
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

  private partial def skipObject : Parser Unit := do
    skipStringToken; ws; skipChar ':'; ws
    skipValue; ws
    match ← any with
    | '}' => pure ()
    | ',' => ws; skipObject
    | _ => fail "expected ',' or '}'"
end

private def token : Parser Slice := do
  let start ← position
  skipValue
  let stop ← position
  pure ⟨start, stop.2.offset⟩

/-- Validate JSON syntax without constructing a JSON value tree. -/
def parse (source : String) : Except String Slice :=
  (do ws; let value ← token; ws; eof; pure value : Parser Slice).run source

private def Slice.read (value : Slice) (parser : Parser α) : Except String α :=
  match parser value.start with
  | .error it error => .error s!"offset {it.2.offset.byteIdx}: {error}"
  | .success it result =>
    if it.2.offset == value.stop then .ok result
    else .error s!"offset {it.2.offset.byteIdx}: expected end of JSON token"

private partial def arrayItems (values : Array Slice) : Parser (Array Slice) := do
  let value ← token
  ws
  match ← any with
  | ']' => pure (values.push value)
  | ',' => ws; arrayItems (values.push value)
  | _ => fail "expected ',' or ']'"

/-- Return borrowed elements; nested values remain unmaterialized. -/
def Slice.array (value : Slice) : Except String (Array Slice) := value.read do
  skipChar '['; ws
  if (← peek!) == ']' then skip; pure #[] else arrayItems #[]

private partial def objectFields (fields : Array (String × Slice)) :
    Parser (Array (String × Slice)) := do
  skipChar '"'
  let key ← Lean.Json.Parser.str
  ws; skipChar ':'; ws
  let value ← token
  let fields := (fields.filter (fun field => field.1 != key)).push (key, value)
  ws
  match ← any with
  | '}' => pure fields
  | ',' => ws; objectFields fields
  | _ => fail "expected ',' or '}'"

/-- Duplicate members retain their last value, matching Lean's JSON parser. -/
def Slice.object (value : Slice) : Except String (Array (String × Slice)) := value.read do
  skipChar '{'; ws
  if (← peek!) == '}' then skip; pure #[] else objectFields #[]

def Slice.optionalField (value : Slice) (name : String) : Except String (Option Slice) := do
  pure (((← value.object).find? (fun field => field.1 == name)).map Prod.snd)

def Slice.field (value : Slice) (name : String) : Except String Slice := do
  let some field ← value.optionalField name | throw s!"missing field `{name}`"
  pure field

def Slice.string (value : Slice) : Except String String :=
  value.read (skipChar '"' *> Lean.Json.Parser.str)

def Slice.number (value : Slice) : Except String Lean.JsonNumber :=
  value.read Lean.Json.Parser.num

def Slice.natural (value : Slice) : Except String Nat := do
  let number ← value.number
  match number with
  | ⟨.ofNat result, 0⟩ => pure result
  | _ => throw "expected unsigned integer"

def Slice.integer (value : Slice) : Except String Int := do
  let number ← value.number
  if number.exponent == 0 then pure number.mantissa
  else throw "expected integer"

def Slice.boolean (value : Slice) : Except String Bool := value.read do
  match ← peek! with
  | 't' => skipString "true"; pure true
  | 'f' => skipString "false"; pure false
  | _ => fail "expected boolean"

def Slice.isNull (value : Slice) : Bool :=
  (value.read (skipString "null")).isOk

end Miri.Input.JsonReader
