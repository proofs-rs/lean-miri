import empty_function.BodyStep

/-! The canonical ghost validation scope on the fieldless unit local. This is
an internal composition lemma; its query premises are discharged from pure
compiler metadata and actual dictionary equations by the assignment theorem. -/
namespace EmptyFunction.BodyValidation
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
variable {K U C F A Pad : Type}

def active (state : ValidityMachine.State K U) : ValidityMachine.State K U :=
  {state with machine := {state.machine with user := {state.machine.user with payload :=
    {state.machine.user.payload with ghost := true}}}}

def session (name : String) : ValidityVisitor.Session Provenance := {
  path := ⟨name,#[]⟩, flags := ⟨true,false⟩, ctfeMode := none,
  refTracking := none, dataBytes := none }

theorem shallow_fieldless
    (h : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A Pad)
    (choice : C) (fuel : Nat) (state : ValidityMachine.State K U)
    (place : RuntimePlace Provenance) (name : String)
    (noGhost : state.machine.user.payload.ghost = false)
    (ghost : @h.withGhostValidation = @ValidityMachine.withGhostValidation K U)
    (nameQuery : h.typeName choice place.layout.ty state = .ok name state)
    (readQuery : h.toOp choice place (active state) =
      .ok ⟨.immediate .uninit,place.layout⟩ (active state))
    (classify : h.classify choice place.layout.ty (active state) =
      .ok (.aggregate false false false) (active state))
    (inhabited : h.opsemInhabited choice place.layout.ty (active state) = .ok true (active state))
    (fields : place.layout.layout.fields = .Arbitrary #[] #[])
    (variants : place.layout.layout.variants = .Single 0)
    (debugOff : h.debugAssertions = false) :
    ValidityVisitor.validatePlace h choice (fuel+1) place false true state = .ok () state := by
  have visited := ValidityVisitor.visit_fieldless h choice fuel (session name) place (active state)
    0 classify inhabited fields variants rfl debugOff
  unfold ValidityVisitor.validatePlace
  simp only [ghost, bind, Bind.bind, EStateM.bind, nameQuery,
    ValidityMachine.withGhostValidation, noGhost, Bool.false_eq_true, ↓reduceIte]
  simp only [active, session] at readQuery visited
  simp only [readQuery, pure, Pure.pure, EStateM.pure, visited,
    ValidityVisitor.resetPadding_no_ranges,
    bind, Bind.bind, EStateM.bind]
  cases state
  simp_all
  rename_i stack machine
  rw [←noGhost]

end EmptyFunction.BodyValidation
