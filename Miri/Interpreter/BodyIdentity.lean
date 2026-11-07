import Miri.MIR.SyntaxTables

/-! Identity of an actual compiler MIR body in the fixed program's body table.
This is independent of structural body equality, diagnostic names or spans. -/
namespace Miri.Interpreter

structure BodyIdentity where
  private mk ::
  index : Nat
  deriving DecidableEq, Repr

namespace BodyIdentity
/-- Called by the program loader with its exact compilation-local body key. -/
def ofCanonicalIndex (index : Nat) : BodyIdentity := ⟨index⟩
end BodyIdentity

structure LoadedBody where
  private mk ::
  identity : BodyIdentity
  bodyId : MIR.BodyId
  body : MIR.BodyNode
  tables : MIR.SyntaxTables
  deriving DecidableEq, Repr

def LoadedBody.ofTables (identity : BodyIdentity) (tables : MIR.SyntaxTables) (id : MIR.BodyId) :
    Except String LoadedBody := do
  let body ← (tables.bodies.lookup id.index).mapError (fun id => s!"invalid MIR body ID {id}")
  unless body.alwaysLive.all (fun localId => localId > body.argumentCount && localId < body.locals.size) do
    throw "invalid MIR always-live local cache"
  return ⟨identity, id, body, tables⟩

/-- The input reader's range/filter construction satisfies the loader check. -/
theorem LoadedBody.alwaysLive_filter_valid (localCount argumentCount : Nat)
    (unannotated : Nat → Bool) :
    ((Array.range localCount).filter (fun id => id > argumentCount && unannotated id)).all
      (fun id => id > argumentCount && id < localCount) = true := by
  rw [Array.all_eq_true']
  intro id selected
  obtain ⟨inRange, included⟩ := Array.mem_filter.mp selected
  have bounded := Array.mem_range.mp inRange
  simp only [Bool.and_eq_true, decide_eq_true_eq] at included ⊢
  exact ⟨included.1, bounded⟩

/-- Loading rejects cached locals outside the non-argument local range. -/
theorem LoadedBody.ofTables_alwaysLive (identity : BodyIdentity) (tables : MIR.SyntaxTables)
    (id : MIR.BodyId) (loaded : LoadedBody)
    (success : LoadedBody.ofTables identity tables id = .ok loaded) :
    loaded.body.alwaysLive.all
      (fun localId => localId > loaded.body.argumentCount && localId < loaded.body.locals.size) = true := by
  unfold LoadedBody.ofTables at success
  cases lookup : tables.bodies.lookup id.index with
  | error reason => simp [lookup, Except.mapError, bind, Except.bind] at success
  | ok node =>
    simp only [lookup, Except.mapError, bind, Except.bind] at success
    by_cases valid : node.alwaysLive.all
        (fun localId => localId > node.argumentCount && localId < node.locals.size) = true
    · simp [valid, pure, Except.pure] at success
      subst loaded
      exact valid
    · simp [valid, pure, Except.pure] at success

end Miri.Interpreter
