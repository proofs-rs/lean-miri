import Miri.Input.CompilerInitialCtfeQueryStore
import Miri.Input.CompilerInitialCtfeRootEngine

/-! Fixed production engine wrapper; raw runtime leaves receive this capability
explicitly instead of importing EvalConfigurationCore through EvalWorld. -/
namespace Miri.Input.CompilerInitialCtfeQueryProvider
abbrev Answer := CompilerInitialCtfeQueryStore.Answer
abbrev State := CompilerInitialCtfeQueryStore.State
abbrev Memo := CompilerInitialCtfeQueryStore.Memo
abbrev init := CompilerInitialCtfeQueryStore.init
abbrev cached := CompilerInitialCtfeQueryStore.cached
abbrev memoSize := CompilerInitialCtfeQueryStore.memoSize
def evaluate (key : CtfeQueryBridge.QueryKey) : CtfeQueryBridge.Action State String Answer :=
  CompilerInitialCtfeQueryStore.evaluateWith CompilerInitialCtfeRootEngine.run key
end Miri.Input.CompilerInitialCtfeQueryProvider
