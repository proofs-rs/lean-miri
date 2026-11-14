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

/-- Physical references carried by every raw MIR region constructor. -/
def regionReferencesValid (definitions : Nat) : MIR.Region → Bool
  | .Bound _ _ (.Named id) | .Placeholder _ _ (.Named id) => id < definitions
  | .LateParameter scope (.Named id) => scope < definitions && id < definitions
  | .LateParameter scope _ => scope < definitions
  | .Bound .. | .Placeholder .. | .EarlyParameter .. | .Static | .InferenceVariable .. | .Erased | .Error => true

private def sourceVariableValid (definitions : Nat) : MIR.BoundVariableKind → Bool
  | .Type (.Param id) | .Region (.Named id) => id < definitions
  | _ => true

private def sourceArgumentValid (types constants definitions : Nat) : MIR.GenericArg → Bool
  | .Type id => id < types
  | .Const id => id < constants
  | .Lifetime region => regionReferencesValid definitions region

/-- Every source predicate belongs to these exact child and physical-definition
pools. In particular an empty type/constant universe cannot retain dangling rows. -/
def predicatePoolValid (types : Array TypeNode) (constants : Array MIR.TypeConst)
    (definitions : Array DefinitionId) (predicates : Array VtablePredicate) : Bool :=
  let rows := predicates.all fun predicate =>
    predicate.definitionId < definitions.size &&
    predicate.genericArgs.all (sourceArgumentValid types.size constants.size definitions.size) &&
    predicate.boundVariables.all (sourceVariableValid definitions.size) &&
    (match predicate.kind, predicate.projectionTerm with
      | .trait, none => true
      | .autoTrait, none => predicate.genericArgs.isEmpty
      | .projection, some (.type id) => id < types.size
      | .projection, some (.constant id) => id < constants.size
      | _, _ => false)
  let unique := predicates.zipIdx.all fun (predicate,index) =>
    !(predicates.extract 0 index).any fun other =>
      other.kind == predicate.kind && other.definitionId == predicate.definitionId &&
      other.genericArgs == predicate.genericArgs && other.boundVariables == predicate.boundVariables &&
      other.projectionTerm == predicate.projectionTerm
  rows && unique && types.all fun node => match node.shape with
    | .dynamicTraitObject ids principal region =>
      !ids.isEmpty && ids.all (· < predicates.size) &&
      principal == ids.find? (fun id => (predicates[id]?).any (·.kind == .trait)) &&
      regionReferencesValid definitions.size region
    | _ => true

structure CheckedMaterial (types : Array TypeNode) (constants : Array MIR.TypeConst)
    (definitions : Array DefinitionId) (predicates : Array VtablePredicate) (pointerBytes : Nat) where
  private mk ::
  predicateValidity : PLift (predicatePoolValid types constants definitions predicates = true)
  density : PLift (isDense types = true)
  definitionIndex : Std.HashMap (Nat × Nat) DefinitionRef
  indexComplete : PLift (definitionIndexComplete definitions definitionIndex = true)
  positivePointerBytes : PLift (pointerBytes > 0)

def CheckedMaterial.create (types : Array TypeNode) (constants : Array MIR.TypeConst)
    (definitions : Array DefinitionId) (predicates : Array VtablePredicate) (pointerBytes : Nat) :
    Except String (CheckedMaterial types constants definitions predicates pointerBytes) := do
  if valid : predicatePoolValid types constants definitions predicates = true then
   if positive : pointerBytes > 0 then
     if dense : isDense types = true then
       let mut index : Std.HashMap (Nat × Nat) DefinitionRef := {}
       for (definition,position) in definitions.zipIdx do
         index := index.insert (definition.crateIndex,definition.index) position
       if complete : definitionIndexComplete definitions index = true then
         pure ⟨⟨valid⟩,⟨dense⟩,index,⟨complete⟩,⟨positive⟩⟩
       else throw "type universe physical definition is duplicated"
     else throw "material type ID/index mismatch"
   else throw "type universe target pointer width is zero"
  else throw "type universe source predicate pool is malformed, duplicated or dangling"

/-- Every index hit is checked against its exact source row. Failure has one
uniform absence diagnostic; there is no linear or compiler-answer fallback. -/
def CheckedMaterial.definitionRef {types constants definitions predicates pointerBytes}
    (checked : CheckedMaterial types constants definitions predicates pointerBytes)
    (wanted : DefinitionIdentity) : Except String DefinitionRef := do
  let some id := checked.definitionIndex[(wanted.crateIndex,wanted.index)]?
    | throw "type universe physical definition is absent or duplicated"
  let some actual := definitions[id]?
    | throw "type universe physical definition is absent or duplicated"
  if actual.crateIndex = wanted.crateIndex ∧ actual.index = wanted.index then
    pure id
  else throw "type universe physical definition is absent or duplicated"

theorem CheckedMaterial.definitionRef_sound {types constants definitions predicates pointerBytes}
    (checked : CheckedMaterial types constants definitions predicates pointerBytes)
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
