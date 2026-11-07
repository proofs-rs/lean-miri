import Miri.Interpreter.Rvalue
import Miri.MIR.SyntaxTables

namespace Miri.Interpreter.RvalueTable

def eval (tables : MIR.SyntaxTables)
    (hooks : RvalueHooks P S C V MIR.PlaceId MIR.OperandId MIR.AggregateNode MIR.OperandListId)
    (choice : C) (value : MIR.RvalueId) (destination : MIR.PlaceId) : RvalueM S Unit := do
  let rvalue ← match tables.rvalues.lookup value.index with
    | .ok rvalue => pure rvalue
    | .error _ => throw (.invalidProgram s!"invalid MIR rvalue ID {value.index}")
  evalRvalueIntoPlace hooks choice rvalue destination

theorem eval_invalid_rvalue (tables : MIR.SyntaxTables)
    (hooks : RvalueHooks P S C V MIR.PlaceId MIR.OperandId MIR.AggregateNode MIR.OperandListId)
    (choice : C) (value : MIR.RvalueId) (destination : MIR.PlaceId)
    (absent : tables.rvalues.lookup value.index = .error value.index) :
    eval tables hooks choice value destination =
      (throw (.invalidProgram s!"invalid MIR rvalue ID {value.index}") : RvalueM S Unit) := by
  simp only [eval, absent]
  rfl

/-- Successful lookup delegates to the unchanged rvalue operation. -/
theorem eval_known {P S C V : Type} (tables : MIR.SyntaxTables)
    (hooks : RvalueHooks P S C V MIR.PlaceId MIR.OperandId MIR.AggregateNode MIR.OperandListId)
    (choice : C) (id : MIR.RvalueId) (destination : MIR.PlaceId) (node : MIR.RvalueNode)
    (selected : tables.rvalues.lookup id.index = .ok node) :
    eval tables hooks choice id destination = evalRvalueIntoPlace hooks choice node destination := by
  simp only [eval, selected]
  rfl

end Miri.Interpreter.RvalueTable
