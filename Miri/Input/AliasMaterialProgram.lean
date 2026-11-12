import Miri.Input.AliasMaterial
import Miri.Input.AliasNormalization

namespace Miri.Input.AliasMaterial
open GenericSubstitution

/-- Require actual source RHS material before creating a reduction rule.
Abstract declarations are not successful empty aliases. -/
def rule (declaration : Declaration) (template : Option DefinitionTemplate) :
    Except String AliasNormalization.Rule := do
  unless declaration.hasValue do throw "alias declaration has no source RHS"
  let some template := template | throw "alias source RHS template absent"
  pure ⟨declaration.definition, template⟩

/-- Construct only the non-selected declaration index. Actual impl selection,
default inheritance and argument translation stay in the trait engine. -/
def program (source : Array (Declaration × Option DefinitionTemplate)) :
    Except String AliasNormalization.Program := do
  let mut seen : Array DefinitionIdentity := #[]
  let mut freeRules := #[]
  let mut associatedDeclarations := #[]
  for (declaration, template) in source do
    if seen.contains declaration.definition then throw "duplicate source alias declaration"
    seen := seen.push declaration.definition
    if declaration.hasValue then
      let _ ← rule declaration template
    else unless template.isNone do throw "abstract alias declaration unexpectedly has RHS template"
    match declaration.kind with
    | .free true => freeRules := freeRules.push (← rule declaration template)
    | .free false => pure ()
    | .associated .trait parent count _ =>
      associatedDeclarations := associatedDeclarations.push ⟨declaration.definition,parent,count⟩
    | .associated (.traitImpl _) .. | .associated .inherentImpl .. => pure ()
  pure ⟨freeRules, associatedDeclarations⟩

end Miri.Input.AliasMaterial
