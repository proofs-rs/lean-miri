import Miri.Memory.AllocAddresses.AddressGenerator

open Miri.ABI Miri.Memory.AllocAddresses

private def sz (n : Nat) : Size := Size.ofBytes (UInt64.ofNat n)
private def algn (exponent : Nat) : Align := ⟨exponent⟩

private def stateText (generator : AddressGenerator) : String :=
  s!"{generator.getRemaining.start}:{generator.getRemaining.stop}"

private def observe (tag : String) (generator : AddressGenerator)
    (size alignment : Nat) (slack : Fin 16) : IO AddressGenerator := do
  let result := generator.generate (sz size) (algn alignment) slack
  let outcome := match result.outcome with
    | .ok address => s!"O {address}"
    | .error (.alignmentRoundingOverflow ..) => "P"
    | .error _ => "E"
  IO.println s!"G {tag} {outcome} {stateText result.state}"
  return result.state

def main : IO Unit := do
  let mut generator := AddressGenerator.new 100 1000
  generator ← observe "generator-1" generator 5 2 ⟨0, by decide⟩
  generator ← observe "generator-2" generator 3 3 ⟨5, by decide⟩
  generator ← observe "zero-sized" generator 0 0 ⟨0, by decide⟩

  let mut exactEnd := AddressGenerator.new 100 105
  exactEnd ← observe "exact-fit" exactEnd 5 0 ⟨0, by decide⟩
  exactEnd ← observe "past-end" exactEnd 1 0 ⟨0, by decide⟩

  let mut slackOverflow := AddressGenerator.new (18446744073709551615 - 8) 18446744073709551615
  slackOverflow ← observe "slack-overflow" slackOverflow 1 0 ⟨15, by decide⟩

  let mut alignOverflow := AddressGenerator.new (18446744073709551615 - 3) 18446744073709551615
  alignOverflow ← observe "align-overflow" alignOverflow 1 3 ⟨0, by decide⟩

  let mut allocationOverflow := AddressGenerator.new (18446744073709551615 - 1) 18446744073709551615
  allocationOverflow ← observe "allocation-overflow" allocationOverflow 4 0 ⟨0, by decide⟩

  let mut alignedPastEnd := AddressGenerator.new 100 102
  alignedPastEnd ← observe "aligned-past-end" alignedPastEnd 1 3 ⟨0, by decide⟩

  let mut zeroGap := AddressGenerator.new 1 3
  zeroGap ← observe "zero-gap-1" zeroGap 0 0 ⟨0, by decide⟩
  zeroGap ← observe "zero-gap-2" zeroGap 0 0 ⟨0, by decide⟩
  zeroGap ← observe "zero-gap-3" zeroGap 0 0 ⟨0, by decide⟩

theorem slack_choices_preserve_source_range (slack : Fin 16) :
    AddressGenerator.legalSlack slack := AddressGenerator.slack_is_legal slack
