import Miri.Input.DynamicPredicate
import Miri.Input.StableSipHash

/-! Pinned TyKind::Dynamic and Binder<ExistentialPredicate> stable hashing.
The caller supplies raw child streams after whole-root region anonymization;
a child's final TypeId is never accepted as its constructor stream. -/
namespace Miri.Input.DynamicStableHash
open DynamicPredicate
private def le (width value : Nat) : ByteArray :=
  ⟨(Array.range width).map (fun index => UInt8.ofNat (value / 2^(8*index)))⟩
private def tag (value : Nat) : ByteArray := le 1 value
private def fingerprint (bytes : ByteArray) : ByteArray := le 16 (StableSipHash.hash bytes).toNat

private def argumentsBytes (typeBytes constantBytes : Nat → Except String (Option ByteArray))
    (regionBytes : MIR.Region → Except String ByteArray) (arguments : Array MIR.GenericArg) :
    Except String (Option ByteArray) := do
  let mut bytes := le 8 arguments.size
  for argument in arguments do
    match argument with
    | .Type id =>
      let some value ← typeBytes id | return none
      bytes := bytes ++ tag 1 ++ value
    | .Const id =>
      let some value ← constantBytes id | return none
      bytes := bytes ++ tag 2 ++ value
    | .Lifetime region => bytes := bytes ++ tag 0 ++ (← regionBytes region)
  pure (some (fingerprint bytes))

private def predicateBytes (definitionBytes : GenericSubstitution.DefinitionIdentity → Except String ByteArray)
    (typeBytes constantBytes : Nat → Except String (Option ByteArray))
    (regionBytes : MIR.Region → Except String ByteArray) (predicate : Predicate) :
    Except String (Option ByteArray) := do
  let mut variables := le 8 predicate.variables.size
  for boundVariable in predicate.variables do
    match boundVariable with
    | .region .anonymous => variables := variables ++ tag 1 ++ tag 0
    | _ => return none
  let body ← match predicate.body with
    | .trait definition arguments =>
      let some arguments ← argumentsBytes typeBytes constantBytes regionBytes arguments | return none
      pure (tag 0 ++ (← definitionBytes definition) ++ arguments)
    | .autoTrait definition => pure (tag 2 ++ (← definitionBytes definition))
    | .projection definition arguments term =>
      let some arguments ← argumentsBytes typeBytes constantBytes regionBytes arguments | return none
      let term ← match term with
        | .type id =>
          let some value ← typeBytes id | return none
          pure (tag 0 ++ value)
        | .constant id =>
          let some value ← constantBytes id | return none
          pure (tag 1 ++ value)
      pure (tag 1 ++ (← definitionBytes definition) ++ arguments ++ term)
  pure (some (body ++ fingerprint variables))

def sourceBytes (definitionBytes : GenericSubstitution.DefinitionIdentity → Except String ByteArray)
    (typeBytes constantBytes : Nat → Except String (Option ByteArray))
    (regionBytes : MIR.Region → Except String ByteArray) (value : DynamicPredicate.Dynamic) :
    Except String (Option ByteArray) := do
  unless !value.predicates.isEmpty do throw "dynamic stable hash requires a nonempty source predicate list"
  let mut bytes := le 8 value.predicates.size
  for predicate in value.predicates do
    let some predicate ← predicateBytes definitionBytes typeBytes constantBytes regionBytes predicate
      | return none
    bytes := bytes ++ predicate
  pure (some (tag 16 ++ fingerprint bytes ++ (← regionBytes value.region)))
end Miri.Input.DynamicStableHash
