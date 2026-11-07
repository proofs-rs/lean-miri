import Miri.Interpreter.PlaceDynamic
import Miri.MIR.SyntaxTables

namespace Miri.Interpreter.PlaceTable
open Miri.ABI Miri.Memory

private def entry (table : MIR.SharedTable α) (id : Nat) (kind : String) : PlaceM S α := do
  match table.lookup id with
  | .ok value => pure value
  | .error _ => throw (.invalidProgram s!"invalid MIR {kind} ID {id}")

def eval [PointerProvenance P] (tables : MIR.SyntaxTables)
    (hooks : PlaceProjectionHooks P S C E)
    (checkType : C → MIR.PlaceId → RuntimePlace P → PlaceM S Unit)
    (choice : C) (id : MIR.PlaceId) (skipValidityForSimpleDeref : Bool) : PlaceM S (RuntimePlace P) := do
  let node ← entry tables.places id.index "place"
  let projections ← entry tables.projectionLists node.projection.index "projection list"
  let mut place ← localToPlace hooks.place choice node.localId
  if skipValidityForSimpleDeref && projections.size == 1 then
    let some projection := projections[0]? | throw (.invalidProgram "singleton MIR projection list is empty")
    if (← entry tables.projections projection.index "projection") == .Deref then
      return ← hooks.place.deref choice place true
  for projection in projections do
    place ← PlaceDynamic.project hooks choice place (← entry tables.projections projection.index "projection")
  checkType choice id place
  return place

theorem eval_invalid_place [PointerProvenance P] (tables : MIR.SyntaxTables)
    (hooks : PlaceProjectionHooks P S C E)
    (checkType : C → MIR.PlaceId → RuntimePlace P → PlaceM S Unit)
    (choice : C) (id : MIR.PlaceId) (skip : Bool)
    (absent : tables.places.lookup id.index = .error id.index) :
    eval tables hooks checkType choice id skip =
      (throw (.invalidProgram s!"invalid MIR place ID {id.index}") : PlaceM S (RuntimePlace P)) := by
  simp only [eval, entry, absent]
  rfl

/-- A checked empty projection list follows the ordinary local-place path. -/
theorem eval_empty {P S C E : Type} [PointerProvenance P]
    (tables : MIR.SyntaxTables) (hooks : PlaceProjectionHooks P S C E)
    (checkType : C → MIR.PlaceId → RuntimePlace P → PlaceM S Unit)
    (choice : C) (id : MIR.PlaceId) (node : MIR.PlaceNode)
    (selected : tables.places.lookup id.index = .ok node)
    (projections : tables.projectionLists.lookup node.projection.index = .ok #[])
    (check : ∀ place, checkType choice id place = pure ())
    (sourceCheck : ∀ place, hooks.place.checkPlaceType choice ⟨node.localId,#[]⟩ place = pure ()) :
    eval tables hooks checkType choice id true =
      PlaceDynamic.evalPlace hooks choice ⟨node.localId,#[]⟩ true := by
  simp [eval, entry, selected, projections, check, sourceCheck, PlaceDynamic.evalPlace]

end Miri.Interpreter.PlaceTable
