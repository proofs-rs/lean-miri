import Miri.Input.Model.SourceMirUses

/-! Pinned deduce_param_attrs::DeduceParamAttrs over validated generic MIR use
syntax. This is a demand calculation, not stored compiler-derived attributes. -/
namespace Miri.Input.SourceParamAttrs
open SourceMirUses

structure Usage where
  dropped : Bool := false
  sharedBorrowed : Bool := false
  mutated : Bool := false
  captured : Bool := false
  deriving Repr, DecidableEq

/-- Exact visitor effect for one return place/argument. A dereference-first
projection uses the pointee instead of the parameter's indirect storage. -/
def parameterUsage (body : SourceMirUses.Body) (parameter : Nat) : Except String Usage := do
  unless body.phase == .known (.Runtime .Optimized) do
    throw "typed ABI attribute deduction requires optimized MIR source"
  unless parameter ≤ body.argumentCount do throw "typed ABI attribute parameter outside MIR signature"
  let mut usage : Usage := { mutated := parameter == 0 }
  for event in body.events do
    match event.kind with
    | .tailCall => usage := {usage with mutated := true,captured := true}
    | .callMove place =>
      if place.localId == parameter && place.firstProjection != some .deref then
        usage := {usage with mutated := true,captured := true}
    | .place place context =>
      if place.localId == parameter && place.firstProjection != some .deref then
        match context with
        | .nonUse => pure ()
        | .mutating .drop =>
          if place.firstProjection.isNone then usage := {usage with dropped := true}
          else usage := {usage with mutated := true,captured := true}
        | .mutating .store | .mutating .setDiscriminant | .mutating .asmOutput | .mutating .projection =>
          usage := {usage with mutated := true}
        | .mutating .call | .mutating .yield | .mutating .borrow | .mutating .rawBorrow |
          .nonMutating .rawBorrow => usage := {usage with mutated := true,captured := true}
        | .nonMutating .sharedBorrow => usage := {usage with sharedBorrowed := true,captured := true}
        | .nonMutating .inspect | .nonMutating .copy | .nonMutating .move |
          .nonMutating .fakeBorrow | .nonMutating .placeMention | .nonMutating .projection => pure ()
  return usage
end Miri.Input.SourceParamAttrs
