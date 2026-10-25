import Miri.Input.LowerMIR

open Miri.Input

/-- The allocation-free lookup preserves the first matching identity, even in
manually assembled tables containing duplicates, and the exact missing-ID error.
This theorem covers all tables rather than only validated exporter outputs. -/
theorem lookupDefinitionId_eq_list (definitions : Array DefinitionId) (sourceId : DefinitionId) :
    lookupDefinitionId definitions sourceId =
      (match definitions.toList.idxOf? sourceId with
       | some id => pure id
       | none => throw s!"unresolved compiler definition {sourceId.crateIndex}:{sourceId.index}") := by
  have same : definitions.idxOf? sourceId = definitions.toList.idxOf? sourceId := by
    simpa using (List.idxOf?_toArray sourceId definitions.toList)
  simp only [lookupDefinitionId, same]
  rfl

#print axioms lookupDefinitionId_eq_list
