import Lean

namespace Miri.Input.RuntimeMetadata

local instance {p : Prop} : DecidableEq (PLift p) :=
  fun _ _ => isTrue (Subsingleton.elim _ _)

/-- A private, checked certificate that one immutable JSON tree compares equal
to itself. JSON's `BEq` is not assumed lawful: a malformed tree may fail this
test, in which case comparisons must retain their ordinary recursive path. -/
structure JsonReflexivity (left : Lean.Json) where
  private mk ::
  reflexive : Option (PLift ((left == left) = true))
  deriving DecidableEq

namespace JsonReflexivity

def prepare {left : Lean.Json} : JsonReflexivity left :=
  ⟨if h : left == left then some ⟨h⟩ else none⟩

/-- Compare in the source-left orientation, preserving `left == candidate`. -/
def matchesRight {left : Lean.Json} (certificate : JsonReflexivity left) (candidate : Lean.Json) : Bool :=
  match certificate.reflexive with
  | none => left == candidate
  | some ⟨reflexive⟩ =>
      withPtrEq left candidate (fun _ => left == candidate)
        (by intro equal; cases equal; exact reflexive)

/-- Compare in the candidate-left orientation, preserving `candidate == left`. -/
def matchesLeft {left : Lean.Json} (certificate : JsonReflexivity left) (candidate : Lean.Json) : Bool :=
  match certificate.reflexive with
  | none => candidate == left
  | some ⟨reflexive⟩ =>
      withPtrEq candidate left (fun _ => candidate == left)
        (by intro equal; cases equal; exact reflexive)

/-- Optional-cache entry point for callers that keep their historical API. -/
def matchesRightOr {left : Lean.Json} (certificate : Option (JsonReflexivity left)) (candidate : Lean.Json) : Bool :=
  match certificate with
  | none => left == candidate
  | some certificate => certificate.matchesRight candidate

theorem matchesRight_eq {left : Lean.Json} (certificate : JsonReflexivity left) (candidate : Lean.Json) :
    certificate.matchesRight candidate = (left == candidate) := by
  cases h : certificate.reflexive <;>
    simp [matchesRight, h, withPtrEq]

theorem matchesLeft_eq {left : Lean.Json} (certificate : JsonReflexivity left) (candidate : Lean.Json) :
    certificate.matchesLeft candidate = (candidate == left) := by
  cases h : certificate.reflexive <;>
    simp [matchesLeft, h, withPtrEq]

theorem matchesRightOr_eq {left : Lean.Json} (certificate : Option (JsonReflexivity left)) (candidate : Lean.Json) :
    matchesRightOr certificate candidate = (left == candidate) := by
  cases certificate with
  | none => rfl
  | some certificate => exact certificate.matchesRight_eq candidate

end JsonReflexivity

end Miri.Input.RuntimeMetadata
