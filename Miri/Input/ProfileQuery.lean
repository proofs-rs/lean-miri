import Miri.Input.ProfilePreparation
import Miri.Input.CompilerInitialCtfeQueryProvider

/-! Demand-driven selected-root lookup. Catalogue presence never evaluates a
query; only an exact typed query key can select its admitted source. -/
namespace Miri.Input.ProfileQuery
set_option autoImplicit false

def sourceForQuery (prepared : ProfilePreparation.Prepared)
    (key : CtfeQueryBridge.QueryKey) : Except String CompilerInitialCtfeRootSource.Prepared := do
  let .initial _ roots _ := prepared
    | throw "selected compiler CTFE query requires the complete initial profile"
  let matching := roots.filter (fun source => decide (source.query = key))
  let [source] := matching.toList
    | throw "selected compiler CTFE query source is absent or ambiguous"
  pure source

abbrev State := CompilerInitialCtfeQueryProvider.State
abbrev Answer := CompilerInitialCtfeQueryProvider.Answer

/-- Explicit pre-runtime selected-query entry. It owns the complete initial
allocation world and the same extended type universe prepared for those roots. -/
def prepare (prepared : ProfilePreparation.Prepared) : Except String State := do
  let .initial initial roots selected := prepared
    | throw "selected compiler CTFE query requires the complete initial profile"
  unless selected.memos.isEmpty do
    throw "fresh-source public query entry cannot ignore imported initial memo tables; use the run-owned runtime provider"
  unless !roots.isEmpty do throw "selected compiler CTFE query catalogue is empty"
  let [(run,_)] := initial.initialWorld.runs.toList
    | throw "selected compiler CTFE query requires exactly one initial run"
  CompilerInitialCtfeQueryProvider.init initial.compiler initial.image initial.types roots run initial.initialWorld

/-- Demand, not catalogue loading, invokes the real fixed-Step provider.
Its Action returns successor state on errors as well as successful memo hits. -/
def evaluateSelected (key : CtfeQueryBridge.QueryKey) :
    CtfeQueryBridge.Action State String Answer :=
  CompilerInitialCtfeQueryProvider.evaluate key

end Miri.Input.ProfileQuery
