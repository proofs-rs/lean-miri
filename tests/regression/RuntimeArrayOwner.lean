import Miri.Input.Decoder
import Miri.Input.RuntimeArrayFacts

open Miri.Input

private def must {ε α : Type} [ToString ε] (value : Except ε α) : IO α :=
  match value with
  | .ok value => pure value
  | .error reason => throw (IO.userError (toString reason))

private def arrayMust {α : Type} (value : Except RuntimeArrayTypes.Error α) : IO α :=
  match value with
  | .ok value => pure value
  | .error reason => throw (IO.userError (reprStr reason))

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

#eval do
  let decoded ← must (decodeJson (← IO.FS.readFile "examples/empty_function/input.json"))
  let program ← must (lowerProgram decoded.document)
  let owner ← must (RuntimeProgram.ofProgram program)
  -- Diagnostic JSON is not a runtime origin certificate. The typed owner
  -- supplies both compiler queries and constructor layout calculations.
  let owner := {owner with input := {owner.input with raw := .null}}
  let initial ← arrayMust (RuntimeArrayTypes.create owner)
  ensure ((RuntimeArrayFacts.boolean initial initial.byteLayout.ty "is_freeze").toOption == some true)
    "compiler traits use the same typed metadata without consulting diagnostic JSON"
  let tables := initial.metadata.source.compilerFactTables
  let unavailable := {initial with metadata := {initial.metadata with source :=
    {initial.metadata.source with compilerFactTables := {tables with
      booleanValues := tables.booleanValues.map (Option.map fun _ =>
        {status := .unsupported, value := none, reason := some "producer trait obligation"})}}}}
  let preserved := match RuntimeArrayFacts.boolean unavailable unavailable.byteLayout.ty "is_freeze" with
    | .error reason => (reason.splitOn "producer trait obligation").length == 2
    | .ok _ => false
  ensure preserved "unresolved compiler trait remains its demand-local producer failure"
  let (first,world) ← arrayMust (RuntimeArrayTypes.intern initial .u8 3)
  let (again,world) ← arrayMust (RuntimeArrayTypes.intern world .u8 3)
  ensure (first == again) "repeated constructors preserve canonical type identity"
  let (nested,world) ← arrayMust (RuntimeArrayTypes.internElement world first.ty 2)
  let (_,child) ← arrayMust (RuntimeArrayTypes.arrayInfo world nested.ty)
  ensure (child == first) "nested dynamic arrays preserve their actual element type"
  let imported ← arrayMust (RuntimeArrayTypes.lookup world nested.ty)
  ensure (imported == nested) "dynamic type lookup retains constructed layouts"
  ensure ((RuntimeArrayFacts.boolean world nested.ty "is_freeze").toOption == some true)
    "structural traits recurse through runtime constructors"
  ensure ((RuntimeArrayFacts.opsemInhabited world nested.ty 4).toOption == some true)
    "inhabitedness recurses through nested dynamic arrays into compiler evidence"
  let (empty,world) ← arrayMust (RuntimeArrayTypes.internElement world nested.ty 0)
  ensure ((RuntimeArrayFacts.opsemInhabited world empty.ty 1).toOption == some true)
    "zero-length runtime arrays are inhabited without querying their element"
  ensure (RuntimeArrayFacts.opsemInhabited world nested.ty 0).toOption.isNone
    "query budget exhaustion remains a failure"
  ensure (RuntimeArrayFacts.boolean world nested.ty "unsupported_query").toOption.isNone
    "unknown structural queries remain a failure"
  ensure (RuntimeArrayTypes.intern world .u16 (UInt64.ofNat (2^64-1))).toOption.isNone
    "target arithmetic overflow remains a failure"
  IO.println "runtime array shared owner PASS"
