import Miri.Input.SourceEnvironment

open Miri.Input GenericSubstitution TraitSelection SourceEnvironment
private def ancestor : DefinitionIdentity := ⟨0,1⟩
private def child : DefinitionIdentity := ⟨0,2⟩
private def leaf : DefinitionIdentity := ⟨0,3⟩
private def u32 : Term := .atom .type "uint" "u32"
private def usize : Term := .atom .type "uint" "usize"
private def count : Term := .node .constant "value" "" (.ofArray #[usize,.atom .aggregate "scalar" "{\"bytes\":8,\"bits\":4}"])
private def bound (value : Term) : Clause := ⟨#[],.trait ⟨.positive,⟨leaf,#[value]⟩⟩⟩
private def parentMaterial : Material := ⟨#[.type],none,none,false,#[bound (.parameter .type 0)]⟩
private def childMaterial : Material := ⟨#[.type,.constant],some ⟨ancestor,1⟩,some ⟨ancestor,1⟩,false,
  #[⟨#[],.constHasType (.parameter .constant 1) usize⟩]⟩
private def lookup (definition : DefinitionIdentity) : Except String Material :=
  if definition == ancestor then .ok parentMaterial else if definition == child then .ok childMaterial
  else .error "source scope missing"
private def exactly (actual : Except String (Array Clause)) (expected : Array Clause) : Bool :=
  match actual with | .ok clauses => decide (clauses = expected) | .error _ => false
private def rejected (actual : Except String (Array Clause)) : Bool :=
  match actual with | .error _ => true | .ok _ => false
example : exactly (predicates lookup 20 child) (parentMaterial.ownPredicates ++ childMaterial.ownPredicates) = true := by decide +kernel
example : exactly (instantiate lookup 20 child #[u32,count]) #[bound u32,⟨#[],.constHasType count usize⟩] = true := by decide +kernel
example : rejected (instantiate lookup 20 child #[u32]) = true := by decide +kernel
example : rejected (instantiate lookup 20 child #[count,u32]) = true := by decide +kernel
example : rejected (predicates lookup 0 child) = true := by decide +kernel
private def replaceChild (material : Material) : Lookup := fun definition =>
  if definition == child then .ok material else lookup definition
example : rejected (predicates (replaceChild {childMaterial with parent := some ⟨ancestor,0⟩, genericParent := some ⟨ancestor,0⟩}) 20 child) = true := by decide +kernel
example : rejected (predicates (replaceChild {childMaterial with parameters := #[.region,.constant]}) 20 child) = true := by decide +kernel
example : rejected (predicates (replaceChild {childMaterial with parent := some ⟨child,2⟩, genericParent := some ⟨child,2⟩}) 20 child) = true := by decide +kernel
example : rejected (predicates (replaceChild {childMaterial with ownPredicates := #[bound (.parameter .type 3)]}) 20 child) = true := by decide +kernel

private def traitScope : Material := ⟨#[.type,.region,.constant],none,none,true,#[]⟩
example : exactly (predicates (fun _ => .ok traitScope) 20 leaf)
    #[⟨#[],.trait ⟨.positive,⟨leaf,#[.parameter .type 0,.parameter .region 1,.parameter .constant 2]⟩⟩⟩] = true := by decide +kernel
example : rejected (predicates (fun _ => .ok {traitScope with parameters := #[.region]}) 20 leaf) = true := by decide +kernel
