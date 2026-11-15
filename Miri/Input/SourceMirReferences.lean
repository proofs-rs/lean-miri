import Miri.Input.SourceFunctionTypes
import Miri.Input.Model.SourceMir

/-! Demand-local source references. Only syntax of the selected body is visited;
no other body or substitution is enumerated. Global source validity belongs to
the decoder/World boundary. Each canonical handle is interned once per request. -/
namespace Miri.Input.SourceMirReferences
structure Needed where
  types : Array Nat := #[]
  definitions : Array Nat := #[]
  allocations : Array Nat := #[]
  constants : Array SourceMir.Constant := #[]
private def argument (value : SourceTypes.Argument) : Array Nat :=
  match value with
  | .type ref => #[ref]
  | .constant (.value ref _ _) | .constant (.parameter _ (some ref)) => #[ref]
  | _ => #[]
private def place (value : SourceMir.Place) : Array Nat := value.projection.filterMap fun step =>
  match step with | .field _ ref => some ref | _ => none
private def constant (value : SourceMir.Constant) : Needed :=
  let extra := match value.value with
    | .unevaluated _ arguments _ => (arguments.map argument).flatten
    | .typeConstant (.value ref _ _) | .typeConstant (.parameter _ (some ref)) => #[ref]
    | _ => #[]
  let allocations := match value.value with
    | .allocationSlice id _ | .allocationPointer id _ _ _ | .allocationIndirect id _ => #[id]
    | _ => #[]
  ⟨#[value.type] ++ extra,#[],allocations,#[value]⟩
private def operand : SourceMir.Operand → Needed
  | .copy value | .move value => ⟨place value,#[],#[],#[]⟩
  | .constant value => constant value
  | .runtimeChecks _ reference => ⟨#[reference],#[],#[],#[]⟩
  | .unsupported _ => {}
private def append (a b : Needed) : Needed :=
  ⟨a.types ++ b.types,a.definitions ++ b.definitions,a.allocations ++ b.allocations,a.constants ++ b.constants⟩
private def operands (values : Array SourceMir.Operand) : Needed :=
  values.foldl (fun acc value => append acc (operand value)) {}
private def rvalue : SourceMir.Rvalue → Needed
  | .use op _ | .unary _ op => operand op
  | .binary _ a b => append (operand a) (operand b)
  | .reference _ _ value | .rawPointer _ value | .discriminant value => ⟨place value,#[],#[],#[]⟩
  | .pointerCoercion _ op target _ | .cast _ op target =>
    append (operand op) ⟨#[target],#[],#[],#[]⟩
  | .aggregateTuple values => operands values
  | .aggregateArray element values => append (operands values) ⟨#[element],#[],#[],#[]⟩
  | .aggregateClosure definition args values =>
    append (operands values) ⟨(args.map argument).flatten,#[definition],#[],#[]⟩
  | .aggregateAdt definition _ args _ _ values =>
    append (operands values) ⟨(args.map argument).flatten,#[definition],#[],#[]⟩
  | .repeat op expr =>
    let ref := match expr with | .value ref _ _ | .parameter _ (some ref) => #[ref] | _ => #[]
    append (operand op) ⟨ref,#[],#[],#[]⟩
  | .unsupported _ => {}
private def assertion : SourceMir.AssertKind → Needed
  | .boundsCheck a b | .overflow _ a b | .misalignedPointerDereference a b => operands #[a,b]
  | .overflowNeg a | .divisionByZero a | .remainderByZero a | .invalidEnumConstruction a => operand a
  | _ => {}
private def terminator : SourceMir.TerminatorKind → Needed
  | .call fn args destination _ _ _ _ => append (append (operand fn) (operands (args.map (·.operand)))) ⟨place destination,#[],#[],#[]⟩
  | .drop value .. => ⟨place value,#[],#[],#[]⟩
  | .switchInt op .. => operand op
  | .assert condition _ message .. => append (operand condition) (assertion message)
  | _ => {}

def collect (body : SourceMir.Body) : Needed := Id.run do
  let mut result : Needed := ⟨body.locals.map (·.type),#[],#[],#[]⟩
  for value in body.requiredConstants do result := append result (constant value)
  for block in body.blocks do
    for statement in block.statements do
      match statement.kind with
      | .assign destination value =>
        result := append result (append ⟨place destination,#[],#[],#[]⟩ (rvalue value))
      | .placeMention mentioned =>
        result := append result ⟨place mentioned,#[],#[],#[]⟩
      | _ => pure ()
    result := append result (terminator block.terminator.kind)
  return result

structure Pool where
  types : Array (Option Nat)
  definitions : Array (Option Nat)
  allocations : Array Nat
  constants : Array SourceMir.Constant

def prepare (initial : SourceCompilerWorld.World) (body : SourceMir.Body)
    (bindings : Array (Option SourceTypes.Concrete)) (constants : Array (Option Nat)) :
    Except String (SourceCompilerWorld.World × Pool) := do
  let some source := initial.canonical.sourceMaterial | throw "Unsupported MIR source material unavailable"
  let some physical := source.physical | throw "Unsupported MIR source type expressions unavailable"
  let needed := collect body
  let mut world := initial
  let mut types := Array.replicate physical.types.size none
  for ref in needed.types do
    unless ref < types.size do throw "Invalid selected MIR source type reference"
    if types[ref]?.join |>.isNone then
      let (updated,id) ← match physical.types[ref]? with
        | some (.functionDefinition ..) => SourceFunctionTypes.internSource world ref bindings constants
        | some (.functionPointer _) => SourceSignatureTypes.intern world bindings constants #[] ref (eraseFreeRegions := true)
        | _ => do
          let concrete ← SourceTypes.instantiate physical bindings constants ref
          let concrete ← SourceTypes.eraseRegions concrete
          SourcePhysical.intern world concrete
      world := updated
      types := types.setIfInBounds ref (some id)
  let mut definitions := Array.replicate physical.definitions.size none
  for ref in needed.definitions do
    let some declaration := physical.definitions[ref]? | throw "Invalid selected MIR definition reference"
    if definitions[ref]?.join |>.isNone then
      let (updated,id) ← SourceCompilerWorld.internDefinition world declaration.raw
      world := updated
      definitions := definitions.setIfInBounds ref (some id)
  return (world,⟨types,definitions,needed.allocations,needed.constants⟩)
end Miri.Input.SourceMirReferences
