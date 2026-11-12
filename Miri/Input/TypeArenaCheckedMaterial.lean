import Miri.Input.TypeArena
import Miri.Input.GenericSubstitution

/-! Validated immutable source material and its canonical definition index.
There are no runtime constructor pools or compiler query answers here. Parameters
bind the certificate to the exact raw tables and target pointer width. -/
namespace Miri.Input.TypeArena
open GenericSubstitution

def definitionIndexComplete (definitions : Array DefinitionId)
    (index : Std.HashMap (Nat × Nat) DefinitionRef) : Bool :=
  definitions.zipIdx.all fun (definition,position) =>
    index[(definition.crateIndex,definition.index)]? == some position

structure CheckedMaterial (types : Array TypeNode) (_constants : Array MIR.TypeConst)
    (definitions : Array DefinitionId) (pointerBytes : Nat) where
  private mk ::
  density : PLift (isDense types = true)
  definitionIndex : Std.HashMap (Nat × Nat) DefinitionRef
  indexComplete : PLift (definitionIndexComplete definitions definitionIndex = true)
  positivePointerBytes : PLift (pointerBytes > 0)

def CheckedMaterial.create (types : Array TypeNode) (constants : Array MIR.TypeConst)
    (definitions : Array DefinitionId) (pointerBytes : Nat) :
    Except String (CheckedMaterial types constants definitions pointerBytes) := do
  if positive : pointerBytes > 0 then
    if dense : isDense types = true then
      let mut index : Std.HashMap (Nat × Nat) DefinitionRef := {}
      for (definition,position) in definitions.zipIdx do
        index := index.insert (definition.crateIndex,definition.index) position
      if complete : definitionIndexComplete definitions index = true then
        pure ⟨⟨dense⟩,index,⟨complete⟩,⟨positive⟩⟩
      else throw "type universe physical definition is duplicated"
    else throw "material type ID/index mismatch"
  else throw "type universe target pointer width is zero"

/-- Every index hit is checked against its exact source row. Failure has one
uniform absence diagnostic; there is no linear or compiler-answer fallback. -/
def CheckedMaterial.definitionRef {types constants definitions pointerBytes}
    (checked : CheckedMaterial types constants definitions pointerBytes)
    (wanted : DefinitionIdentity) : Except String DefinitionRef := do
  let some id := checked.definitionIndex[(wanted.crateIndex,wanted.index)]?
    | throw "type universe physical definition is absent or duplicated"
  let some actual := definitions[id]?
    | throw "type universe physical definition is absent or duplicated"
  if actual.crateIndex = wanted.crateIndex ∧ actual.index = wanted.index then
    pure id
  else throw "type universe physical definition is absent or duplicated"

theorem CheckedMaterial.definitionRef_sound {types constants definitions pointerBytes}
    (checked : CheckedMaterial types constants definitions pointerBytes)
    (wanted : DefinitionIdentity) (id : DefinitionRef)
    (result : checked.definitionRef wanted = .ok id) :
    ∃ actual, definitions[id]? = some actual ∧
      actual.crateIndex = wanted.crateIndex ∧ actual.index = wanted.index := by
  cases indexed : checked.definitionIndex[(wanted.crateIndex,wanted.index)]? with
  | none => simp [CheckedMaterial.definitionRef, indexed] at result
  | some position =>
    cases row : definitions[position]? with
    | none => simp [CheckedMaterial.definitionRef, indexed, row] at result
    | some actual =>
      by_cases sameIdentity : actual.crateIndex = wanted.crateIndex ∧ actual.index = wanted.index
      · simp [CheckedMaterial.definitionRef, indexed, row, sameIdentity, pure, Except.pure] at result
        cases result
        exact ⟨actual,row,sameIdentity⟩
      · simp [CheckedMaterial.definitionRef, indexed, row, sameIdentity] at result

end Miri.Input.TypeArena
