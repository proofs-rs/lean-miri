import Miri.Input.WorldTypeHash
import Miri.Input.WorldTypeFlags
import Miri.Input.WorldNormalization
open Miri.Input Miri.Input.TypeArena Miri.Input.GenericSubstitution
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def rejects (value : Except String α) (message : String) : IO Unit := do
  if value.isOk then throw (IO.userError message)
private def node (id : Nat) (shape : TypeShape) : TypeNode :=
  {id,shape,display := "dynamic raw control",layoutId := 0}
private def principal : VtablePredicate :=
  {kind := .trait,definitionId := 0,definitionPath := none,genericArgs := #[],boundVariables := #[],projectionTerm := none}
private def sourceTypes := #[node 0 (.uint (.known .u8)),node 1 (.dynamicTraitObject #[0] (some 0) .Erased)]

example {types constants definitions predicates pointerBytes}
    (checked : CheckedMaterial types constants definitions predicates pointerBytes) :
    predicatePoolValid types constants definitions predicates = true :=
  checked.predicateValidity.down

def main : IO Unit := do
  let definitions : Array DefinitionId := #[{crateIndex := 0,index := 8}]
  let world ← must (World.ofMaterial sourceTypes #[] definitions #[principal] 8)
  let some (.dynamic value) ← must (world.materialKey (node 1 (.dynamicTraitObject #[0] (some 0) .Erased)))
    | throw (IO.userError "dynamic material key absent")
  let (reused,_) ← must ((World.internType (.dynamic value)).run world)
  unless reused == 1 do throw (IO.userError "complete dynamic material identity not reused")
  let novel ← must (World.ofMaterial #[] #[] definitions #[] 8)
  let (_,novel) ← must ((World.internType (.dynamic value)).run novel)
  unless novel.materialPredicates.isEmpty do throw (IO.userError "novel dynamic acquired source predicates")
  rejects (World.ofMaterial sourceTypes #[] definitions #[] 8) "dangling predicate accepted"
  rejects (World.ofMaterial sourceTypes #[] definitions #[{principal with definitionId := 1}] 8) "dangling physical definition accepted"
  rejects (World.ofMaterial sourceTypes #[] definitions #[principal,principal] 8) "duplicate source predicate accepted"
  rejects (World.ofMaterial sourceTypes #[] definitions #[{principal with genericArgs := #[.Type 2]}] 8) "dangling type argument accepted"
  rejects (World.ofMaterial sourceTypes #[] definitions #[{principal with genericArgs := #[.Const 0]}] 8) "dangling constant argument accepted"
  rejects (World.ofMaterial #[] #[] definitions #[{principal with genericArgs := #[.Type 0]}] 8) "empty prefix retained dangling source pool"
  rejects (World.ofMaterial sourceTypes #[] definitions #[{principal with boundVariables := #[.Region (.Named 1)]}] 8) "dangling binder definition accepted"
  rejects (World.ofMaterial sourceTypes #[] definitions #[{principal with genericArgs := #[.Lifetime (.Placeholder 0 0 (.Named 1))]}] 8) "dangling placeholder definition accepted"
  rejects (World.ofMaterial sourceTypes #[] definitions #[{principal with genericArgs := #[.Lifetime (.LateParameter 1 .ClosureEnv)]}] 8) "dangling late-parameter scope accepted"
  rejects (World.ofMaterial sourceTypes #[] definitions #[{principal with projectionTerm := some (.type 0)}] 8) "trait term accepted"
  rejects (World.ofMaterial sourceTypes #[] definitions #[{principal with kind := .projection}] 8) "projection without term accepted"
  rejects (World.ofMaterial sourceTypes #[] definitions #[{principal with kind := .projection,projectionTerm := some (.constant 0)}] 8) "dangling const projection accepted"
  rejects (World.ofMaterial #[node 0 (.uint (.known .u8)),node 1 (.dynamicTraitObject #[] none .Erased)] #[] definitions #[principal] 8) "empty dynamic source accepted"
  rejects (World.ofMaterial #[node 0 (.uint (.known .u8)),node 1 (.dynamicTraitObject #[0] none .Erased)] #[] definitions #[principal] 8) "contradictory principal accepted"
  rejects ((World.internType (.dynamic ⟨#[],.Erased⟩)).run novel) "empty constructed dynamic accepted"
  rejects ((World.internType (.dynamic {value with region := .LateParameter 1 .ClosureEnv})).run novel)
    "constructed object lifetime has a dangling scope"
  let badRegion : DynamicPredicate.Predicate := ⟨#[],.trait ⟨0,8⟩ #[.Lifetime (.Placeholder 0 0 (.Named 1))]⟩
  rejects ((World.internType (.dynamic ⟨#[badRegion],.Erased⟩)).run novel)
    "constructed predicate lifetime has a dangling named identity"
  let wrong : DynamicPredicate.Predicate := ⟨#[],.autoTrait ⟨0,99⟩⟩
  rejects ((World.internType (.dynamic ⟨#[wrong],.Erased⟩)).run novel) "absent constructed physical identity accepted"
  let projection := {principal with kind := .projection,projectionTerm := some (.constant 0)}
  let constants : Array Miri.MIR.TypeConst := #[.Value 0 {root := 0,nodes := #[.Leaf 42 1]}]
  let projectedTypes := #[node 0 (.uint (.known .u8)),node 1 (.dynamicTraitObject #[0] none .Erased)]
  let projected ← must (World.ofMaterial projectedTypes constants definitions #[projection] 8)
  let tree ← must (GenericInstantiationWorld.ofType projected 4096 1)
  let (projectedId,projectedNovel) ← must ((GenericInstantiationWorld.resolveType 4096 tree).run
    (← must (World.ofMaterial #[] #[] definitions #[] 8)))
  unless (← must (GenericInstantiationWorld.ofType projectedNovel 4096 projectedId)) == tree do
    throw (IO.userError "Const projection term did not roundtrip outside material prefixes")
  let auto : DynamicPredicate.Predicate := ⟨#[],.autoTrait ⟨0,8⟩⟩
  rejects ((World.internType (.dynamic ⟨#[auto,⟨#[],.trait ⟨0,8⟩ #[]⟩],.Erased⟩)).run novel)
    "misordered auto-trait/principal source accepted"
  let term : Term := .node .type "dynamic" "" (Terms.ofArray #[
    .binder #[] (.definition .aggregate "projection" ⟨0,8⟩ (.cons (.atom .region "erased" "") .nil)),
    .atom .region "erased" ""])
  rejects ((GenericInstantiationWorld.resolveType 4096 term).run novel) "lifetime projection term accepted"
  let bound : Term := .node .type "dynamic" "" (Terms.ofArray #[
    .binder #[.region .anonymous] (.definition .aggregate "trait" ⟨0,8⟩ (.cons
      (.node .type "reference" "immutable" (Terms.ofArray #[.bound .region (.Bound 0) 1 .anonymous,.atom .type "uint" "u8"])) .nil)),
    .atom .region "erased" ""])
  rejects (BinderRegions.eraseAndAnonymizeOpen 4096 bound) "invalid local binder ownership accepted"
  IO.println "PASS dynamic source pool certificate, exact interning, empty-prefix clearing, dangling/duplicate/domain/principal/binder controls"
