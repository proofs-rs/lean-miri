import Miri.Input.TraitSelection.RelevantImpl
import Miri.Input.TraitSelection.Match

/-! Ground structural-auto fragment of the pinned search graph's coinductive
initial response. A backedge is admitted only when the entire cycle consists
of unique structural candidates: positive coinductive auto goals with no
possibly relevant source impl. This requires no inference constraints or
provisional result cache. Other cycles remain outside this fragment. -/
namespace Miri.Input.TraitSelection.StructuralCycle

/-- Return the start of a certified structural cycle, or `none` for an
unsupported cycle. Absence is never a negative trait result. -/
def certify (program : Program) (environment : Environment) (fuel : Nat)
    (active : Array Goal) (goal : Goal) (entryBoundary : Nat := 0) : Except String (Option Nat) := do
  unless environment.assumptions.isEmpty do return none
  let mut start : Option Nat := none
  for index in [:active.size] do
    let some prior := active[index]? | throw "structural cycle active index absent"
    if prior = goal && start.isNone then start := some index
  let some first := start | return none
  if first < entryBoundary then return none
  for index in [first:active.size] do
    let some member := active[index]? | throw "structural cycle member absent"
    unless member.polarity == .positive do return none
    let declarations := program.traits.filter (·.definition == member.traitRef.definition)
    unless declarations.size == 1 do throw "structural cycle declaration missing or ambiguous"
    let some source := declarations[0]? | throw "structural cycle declaration absent"
    unless source.isAuto && source.isCoinductive && !source.isAlias do return none
    unless source.parameters.size == member.traitRef.arguments.size do
      throw "structural cycle trait argument arity mismatch"
    for (parameter, argument) in source.parameters.zip member.traitRef.arguments do
      unless parameter == argument.sort do throw "structural cycle trait argument sort mismatch"
      Match.requireGround fuel argument
    for implementation in source.implementations do
      if ← RelevantImpl.possible fuel implementation member.traitRef then return none
  return some first
end Miri.Input.TraitSelection.StructuralCycle
