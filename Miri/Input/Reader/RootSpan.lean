import Miri.Input.Reader.SourceSpan

namespace Miri.Input.Reader
open Lean Miri.MIR

def Catalog.readRootSpan (catalog : Catalog) (table : SharedTable SourceSpanData) :
    Except String (Option Nat × SharedTable SourceSpanData) := do
  match ← catalog.optionalField catalog.root "compiler_session_queries" "$" with
  | none | some .null => return (none, table)
  | some session =>
    match ← catalog.optionalField session "root_span" "$.compiler_session_queries" with
    | none | some .null => return (none, table)
    | some span =>
      let path := "$.compiler_session_queries.root_span"
      unless ← catalog.boolean (← catalog.field span "is_dummy" path) s!"{path}.is_dummy" do
        throw s!"{path}: compiler root span is not DUMMY_SP"
      let (id, table) ← catalog.readSourceSpan table span path
      return (some id, table)

end Miri.Input.Reader
