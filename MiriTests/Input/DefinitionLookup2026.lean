import Miri.Input.LowerMIR

open Miri.Input

theorem lookupDefinitionId_checked (definitions : Array DefinitionId) (id : Nat) :
    lookupDefinitionId definitions id =
      (if id < definitions.size then .ok id else .error s!"unresolved compiler definition {id}") := by
  by_cases h : id < definitions.size
  · simp [lookupDefinitionId, h, pure, Except.pure]
  · simp only [lookupDefinitionId, h, ↓reduceIte]
    rfl

#print axioms lookupDefinitionId_checked
