import Miri.Input.JsonReader

open Miri.Input.JsonReader

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def expectOk (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def item (values : Array Slice) (index : Nat) : IO Slice :=
  match values[index]? with
  | some value => pure value
  | none => throw (IO.userError "missing array element")

#eval show IO Unit from do
  let root ← expectOk (parse " {\"a\": [0, -5, 1.25e2, true, null, \"\\uD83D\\uDE03\"], \"empty\":{}, \"a\":[7]} ")
  let fields ← expectOk root.object
  check (fields.size == 2) "duplicate keys must retain only their final value"
  let a ← expectOk (root.field "a")
  let items ← expectOk a.array
  check (items.size == 1) "duplicate key must use last value"
  check ((← expectOk (← item items 0).natural) == 7) "natural extraction"
  check ((← expectOk (root.optionalField "missing")).isNone) "missing optional field"
  check (!(root.field "missing").isOk) "missing required field"
  check ((← expectOk (← expectOk (root.field "empty")).object).isEmpty) "empty object"

  let numbers ← expectOk (parse "[0, -5, 1.25e2, 1.0, 1e2, -0]")
  let numbers ← expectOk numbers.array
  check ((← expectOk (← item numbers 0).natural) == 0) "zero"
  check ((← expectOk (← item numbers 1).integer) == -5) "negative integer"
  check (!(← item numbers 1).natural.isOk) "negative natural rejected"
  check ((← expectOk (← item numbers 2).number).mantissa == 125) "exponent number"
  check (!(← item numbers 3).natural.isOk) "decimal representation remains distinct"
  check ((← expectOk (← item numbers 4).natural) == 100) "positive exponent"
  check ((← expectOk (← item numbers 5).natural) == 0) "negative zero"

  let values ← expectOk (parse "[true,false,null,\"\\uD83D\\uDE03\\n\\t\\\\\\\"\"]")
  let values ← expectOk values.array
  check (← expectOk (← item values 0).boolean) "true"
  check (!(← expectOk (← item values 1).boolean)) "false"
  check (← item values 2).isNull "null"
  check (!(← item values 0).isNull) "nonnull"
  check ((← expectOk (← item values 3).string) == "😃\n\t\\\"") "Unicode and escapes"
  check (!(← item values 2).string.isOk) "wrong scalar type"
  check ((← expectOk (← expectOk (parse "\"é日本語\"")).string) == "é日本語") "UTF-8 byte positions"

  for source in ["", " ", "[", "{", "[1,]", "{\"x\":1,}", "[1 2]", "{\"x\" 1}",
      "01", "-", "1.", "1e", "1e+", "true false", "nullx", "\"unterminated",
      "\"\\x\"", "\"\\u12q4\"", "\"line\nfeed\"", "{\"ignored\":[0,{\"x\":tru}]}" ] do
    check (!(parse source).isOk) s!"invalid syntax accepted: {source}"

#eval show IO Unit from do
  let root ← expectOk (parseObject " {\"a\":0,\"nested\":{\"x\":[true,null]},\"a\":7,\"escaped\\u006b\":\"value\"} ")
  check (root.fields.size == 3) "indexed object must retain last duplicate"
  check ((← expectOk (← expectOk (root.field "a")).natural) == 7) "indexed duplicate field"
  check ((← expectOk (← expectOk (root.field "escapedk")).string) == "value") "indexed escaped key"
  check ((← expectOk (root.optionalField "missing")).isNone) "indexed absent member"
  check ((parseObject "[]").isOk == false) "object entrypoint accepted array root"
  check ((parseObject "{\"ignored\":[1,]}").isOk == false) "object entrypoint skipped malformed nested input"
  check ((parseObject "{} null").isOk == false) "object entrypoint accepted trailing token"
