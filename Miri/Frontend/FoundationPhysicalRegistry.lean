import Miri.Frontend.FoundationPhysicalTypes
import Miri.Frontend.FoundationTypeRegistry
import Miri.Frontend.FoundationNominalShape

/-! Demand-local physical pools. Every array child and usize length is interned
before its parent. No input document, compiler-fact catalog or executable entry
point is synthesized by these component tables. -/
namespace Miri.Frontend.Foundation

structure PhysicalTypeRegistry where
  registry : TypeRegistry
  types : Array Input.TypeNode := #[]
  layouts : Array Input.Layout := #[]
  typeConstants : Array MIR.TypeConst := #[]
  predicates : Array Input.VtablePredicate := #[]

namespace PhysicalTypeRegistry

def start (document : Document) : PhysicalTypeRegistry :=
  { registry := TypeRegistry.start document }

/-- Read the exact document-local type/layout pair, rejecting broken identities. -/
def lookup (r : PhysicalTypeRegistry) (id : Nat) : Except String (Input.TypeNode × Input.Layout) := do
  let some node := r.types[id]? | throw "physical type ID absent"
  unless node.id == id do throw "physical type ID/index mismatch"
  let some layout := r.layouts[node.layoutId]? | throw "physical layout ID absent"
  return (node, layout)

private def predicatePath (r : PhysicalTypeRegistry) (definition : Nat) : Except String String := do
  let some row := r.registry.document.definitions[definition]? | throw "dynamic predicate definition absent"
  row.getObjValAs? String "path"

private def internPredicate (r : PhysicalTypeRegistry) (predicate : Input.VtablePredicate) :
    PhysicalTypeRegistry × Nat :=
  match r.predicates.findIdx? (· == predicate) with
  | some id => (r, id)
  | none => ({r with predicates := r.predicates.push predicate}, r.predicates.size)

/-- Materialize only supported demanded types, retaining canonical structural
identity through TypeRegistry. Constants are canonical typed usize valtree leaves. -/
def intern (r : PhysicalTypeRegistry) (ty : ConcreteType) :
    Except String (PhysicalTypeRegistry × Nat) := go 1024 r ty
where
  go (fuel : Nat) (r : PhysicalTypeRegistry) (ty : ConcreteType) :
      Except String (PhysicalTypeRegistry × Nat) := do
    let .succ fuel := fuel | throw "physical registry recursion exhausted"
    -- Validate the full parent before adding any recursively demanded material.
    let layout ← physicalLayoutOfDocument r.registry.document ty
    for i in [:r.registry.entries.size] do
      let some entry := r.registry.entries[i]? | throw "physical registry entry absent"
      if sameConcrete 1024 entry.type ty then
        let _ ← r.lookup i
        return (r, i)
    let (r, references) ← match ty with
      | .array element count => do
        let (r, elementId) ← go fuel r element
        let (r, usizeId) ← go fuel r (.primitive "uint" "usize")
        let target ← runtimeTargetOfTarget r.registry.document.target
        let width := target.base.pointerWidth.bits.toNat / 8
        let constant := MIR.TypeConst.Value usizeId ⟨#[.Leaf count width], 0⟩
        let mut found := none
        for i in [:r.typeConstants.size] do
          if r.typeConstants[i]? == some constant then found := some i
        let (r, constantId) := match found with
          | some id => (r, id)
          | none => ({ r with typeConstants := r.typeConstants.push constant }, r.typeConstants.size)
        pure (r, some (elementId, constantId))
      | _ => pure (r, none)
    let (r, pointeeReference) ← match ty with
      | .pointer _ pointee | .patternNotNull pointee => do
        let (r, pointeeId) ← go fuel r pointee
        pure (r, some pointeeId)
      | _ => pure (r, none)
    let (r, functionReferences) ← match ty with
      | .functionPointer inputs output _ _ _ => do
        let mut next := r
        let mut inputIds := #[]
        for input in inputs do
          let (updated, inputId) ← go fuel next input
          next := updated
          inputIds := inputIds.push inputId
        let (finished, outputId) ← go fuel next output
        pure (finished, some (inputIds, outputId))
      | _ => pure (r, none)
    let (r, dynamicReferences) ← match ty with
      | .dynamicObject source => do
        let mut next := r
        let mut ids := #[]
        let mut principal := none
        if let some definition := source.principal then
          let mut args := #[]
          for ty in source.arguments do
            let (updated, id) ← go fuel next ty
            next := updated
            args := args.push (.Type id)
          let predicate : Input.VtablePredicate := {
            kind := .trait, definitionId := definition, definitionPath := some (← predicatePath next definition),
            genericArgs := args, boundVariables := #[], projectionTerm := none }
          let (updated, id) := internPredicate next predicate
          next := updated
          ids := ids.push id
          principal := some id
        else
          unless source.arguments.isEmpty && source.projections.isEmpty do throw "dynamic arguments lack principal"
        for projection in source.projections do
          let mut args := #[]
          for ty in projection.arguments do
            let (updated, id) ← go fuel next ty
            next := updated
            args := args.push (.Type id)
          let (updated, term) ← go fuel next projection.term
          next := updated
          let predicate : Input.VtablePredicate := {
            kind := .projection, definitionId := projection.definition,
            definitionPath := some (← predicatePath next projection.definition),
            genericArgs := args, boundVariables := #[], projectionTerm := some term }
          let (updated, id) := internPredicate next predicate
          next := updated
          ids := ids.push id
        for definition in source.autoTraits do
          let predicate : Input.VtablePredicate := {
            kind := .autoTrait, definitionId := definition, definitionPath := some (← predicatePath next definition),
            genericArgs := #[], boundVariables := #[], projectionTerm := none }
          let (updated, id) := internPredicate next predicate
          next := updated
          ids := ids.push id
        pure (next, some (ids, principal))
      | _ => pure (r, none)
    let (r, nominalReferences) ← match ty with
      | .nominal definition args => do
        let mut next := r
        let mut argIds := #[]
        for arg in args do
          let (updated, id) ← go fuel next arg
          next := updated
          argIds := argIds.push id
        let fields ← nominalFields r.registry.document definition args
        let mut fieldIds := #[]
        for variant in fields do
          let mut ids := #[]
          for field in variant do
            let (updated, id) ← go fuel next field
            next := updated
            ids := ids.push id
          fieldIds := fieldIds.push ids
        pure (next, some (definition, argIds, fieldIds))
      | _ => pure (r, none)
    let (r, aggregateReferences) ← match ty with
      | .closure definition args => do
        let some row := r.registry.document.definitions[definition]? | throw "closure definition absent"
        unless (← row.getObjValAs? String "kind") == "closure" do throw "closure definition kind mismatch"
        unless args.size ≥ 3 do throw "closure synthetic arguments absent"
        let mut next := r
        let mut ids := #[]
        for arg in args do
          let (updated, id) ← go fuel next arg
          next := updated
          ids := ids.push id
        pure (next, some ids)
      | .tuple fields => do
        let mut next := r
        let mut ids := #[]
        for field in fields do
          let (updated, id) ← go fuel next field
          next := updated
          ids := ids.push id
        pure (next, some ids)
      | _ => pure (r, none)
    let (registry, id) ← r.registry.intern ty
    unless id == r.types.size && id == r.layouts.size do
      throw "physical registry pool identity mismatch"
    let node ← match nominalReferences with
      | some (definition, args, fields) => nominalTypeNode r.registry.document definition id id args fields
      | none => physicalTypeNode ty id id references pointeeReference functionReferences dynamicReferences aggregateReferences
    return ({ r with registry, types := r.types.push node, layouts := r.layouts.push layout }, id)

/-- Resolve source types without changing the identity scheme. -/
def internSource (r : PhysicalTypeRegistry) (sourceId : Nat)
    (types : Array (Option ConcreteType)) (constants : Array (Option Nat)) :
    Except String (PhysicalTypeRegistry × Nat) := do
  let source ← typeExpr r.registry.document sourceId
  r.intern (← instantiate types constants source)

/-- Convert the exact generated row with the existing fixed-interpreter bridge. -/
def runtimeLayout (r : PhysicalTypeRegistry) (id : Nat) : Except String (ABI.TyAndLayout Nat) := do
  let (node, row) ← r.lookup id
  let target ← runtimeTargetOfTarget r.registry.document.target
  return ⟨node.id, ← (Input.RuntimeMetadata.layout target row).mapError toString⟩

end PhysicalTypeRegistry
end Miri.Frontend.Foundation
