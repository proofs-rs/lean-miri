import Miri.Input.CtfeQueryBridge

/-! Execution-owned raw-query lifecycle. Only real provider successes,
TooGeneric and Reported are terminal compiler answers. Capability failures,
internal errors and an unreported cycle request are not cached as answers.
A cycle needs the owning query engine's genuine diagnostic before Reported.
This store has no serialization or cross-execution/global cache. -/
namespace Miri.Input.CtfeQueryMemo
open CtfeQueryBridge
inductive Response (Diagnostic Value : Type) where
  | finished (value : Except (Failure Diagnostic) Value)
  | cycle (active : Array QueryKey)
  deriving Repr
private inductive Entry (Diagnostic Value : Type) where
  | inProgress
  | complete (value : Except (Failure Diagnostic) Value)
structure Store (Diagnostic Value : Type) where
  private mk ::
  private entries : Array (QueryKey × Entry Diagnostic Value)
  private active : Array QueryKey
  private calls : Array QueryKey

def Store.empty : Store D V := ⟨#[],#[],#[]⟩
def Store.count (store : Store D V) : Nat := store.entries.size
def Store.activeCount (store : Store D V) : Nat := store.active.size
def Store.providerCalls (store : Store D V) : Array QueryKey := store.calls

private def terminal : Except (Failure D) V → Bool
  | .ok _ | .error (.tooGeneric _) | .error (.reported ..) => true
  | .error (.unsupported _) | .error (.internal _) => false

def memo (key : QueryKey) (provider : StateM (Store D V) (Response D V)) :
    StateM (Store D V) (Response D V) := do
  let initial ← get
  let found := initial.entries.filter (·.1 == key)
  if found.size > 1 then return .finished (.error (.internal "duplicate CTFE query memo key"))
  if let some (_,entry) := found[0]? then
    return match entry with
      | .inProgress => .cycle (initial.active.push key)
      | .complete value => .finished value
  set {initial with
    entries := initial.entries.push (key,.inProgress)
    active := initial.active.push key
    calls := initial.calls.push key}
  let value ← provider
  let state ← get
  unless state.active == initial.active.push key do
    return .finished (.error (.internal "CTFE query provider corrupted the active query stack"))
  let found := state.entries.filter (·.1 == key)
  let #[( _,.inProgress)] := found
    | return .finished (.error (.internal "CTFE query provider lost its in-progress marker"))
  let entries := state.entries.filter (·.1 != key)
  let entries := match value with
    | .finished answer => if terminal answer then entries.push (key,.complete answer) else entries
    | .cycle _ => entries
  set {state with entries,active := initial.active}
  pure value
end Miri.Input.CtfeQueryMemo
