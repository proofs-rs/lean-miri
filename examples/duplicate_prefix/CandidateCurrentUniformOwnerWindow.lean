import duplicate_prefix.CandidateCurrentGrantResources

/-! A fixed owner selects one loan, pointer, physical allocation and completed
ancestry across its entire nonempty window. This is support for the current-call
consumer, not ordinary-input admission. -/
namespace DuplicatePrefix.CandidateCurrentUniformOwnerWindow
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall
set_option autoImplicit false

theorem same_id {α β : Type} [DecidableEq α]
    (rows : List (α × β)) (unique : (rows.map Prod.fst).Nodup)
    (id : α) (left right : β) (hl : (id,left) ∈ rows) (hr : (id,right) ∈ rows) :
    left = right := by
  induction rows with
  | nil => simp at hl
  | cons row rows ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    simp only [List.mem_cons] at hl hr
    rcases hl with hl | hl
    · subst row
      rcases hr with hr | hr
      · exact (Prod.mk.inj hr).2.symm
      · exact False.elim (unique.1 (List.mem_map.mpr ⟨(id,right),hr,rfl⟩))
    · rcases hr with hr | hr
      · subst row
        exact False.elim (unique.1 (List.mem_map.mpr ⟨(id,left),hl,rfl⟩))
      · exact ih unique.2 hl hr

theorem uniform_window (world : World) (held : ProtectedTags)
    (interpretation : Interpretation)
    (joint : CandidateCurrentGrantResources.Joint world held interpretation)
    (owner : Nat) (id : AllocId) (offset length : Nat)
    (mode : CandidateFreezeContentResources.Mode) (positive : 0 < length)
    (active : ∀ byte, Window id offset length byte →
      interpretation.content byte owner = some ⟨mode,.active⟩) :
    ∃ loan pointer allocation precise,
      interpretation.loans[owner]? = some loan ∧
      interpretation.pointers[loan.pointer]? = some pointer ∧
      pointer.allocation = id ∧ Present world id allocation ∧
      (id,precise) ∈ interpretation.precise.toList ∧
      ∀ byte, Window id offset length byte →
        byte.2 < allocation.len ∧ RawRights allocation held precise pointer byte.2 mode := by
  have first : Window id offset length (id,offset) := ⟨rfl,by omega,by omega⟩
  obtain ⟨loan,pointer,allocation,precise,loanAt,pointerAt,pointerId,present,_,preciseAt,_⟩ :=
    CandidateCurrentGrantResources.active_raw world held interpretation joint
      (id,offset) owner mode (active _ first)
  refine ⟨loan,pointer,allocation,precise,loanAt,pointerAt,pointerId,present,preciseAt,?_⟩
  intro byte inside
  obtain ⟨otherLoan,otherPointer,otherAllocation,otherPrecise,otherLoanAt,otherPointerAt,
      otherId,otherPresent,bound,otherPreciseAt,rights⟩ :=
    CandidateCurrentGrantResources.active_raw world held interpretation joint
      byte owner mode (active byte inside)
  have loanEq : otherLoan = loan := Option.some.inj (otherLoanAt.symm.trans loanAt)
  subst otherLoan
  have pointerEq : otherPointer = pointer := Option.some.inj (otherPointerAt.symm.trans pointerAt)
  subst otherPointer
  have byteId : byte.1 = id := inside.1
  rw [byteId] at otherPresent otherPreciseAt
  have allocationEq := same_id world.toList joint.shape.1 id otherAllocation allocation
    otherPresent present
  have preciseEq := same_id interpretation.precise.toList joint.shape.2.1 id otherPrecise precise
    otherPreciseAt preciseAt
  subst otherAllocation
  subst otherPrecise
  exact ⟨bound,rights⟩

/-- The selected instance and its completed physical support are uniform over
the owner window. Pointer value equality remains explicit at the call boundary. -/
def UniformOwner (world : World) (held : ProtectedTags) (interpretation : Interpretation)
    (owner : Nat) (id : AllocId) (offset length : Nat)
    (mode : CandidateFreezeContentResources.Mode) (pointer : PointerInstance) : Prop :=
  ∃ loan allocation precise,
    interpretation.loans[owner]? = some loan ∧
    interpretation.pointers[loan.pointer]? = some pointer ∧
    pointer.allocation = id ∧ Present world id allocation ∧
    (id,precise) ∈ interpretation.precise.toList ∧
    ∀ byte, Window id offset length byte →
      byte.2 < allocation.len ∧ RawRights allocation held precise pointer byte.2 mode

theorem positive_call_uniform (before : Before) (held : ProtectedTags)
    (data : Identities) (call : CallLoans)
    (argument : DuplicatePrefixSliceArgument.Argument) (len : UInt64)
    (place : Miri.Interpreter.MPlaceTy Provenance)
    (joint : CandidateCurrentGrantResources.Joint (ActualWorld before) held data.interpretation)
    (actual : ActualBindings before argument len place held call data)
    (normalized : NormalizedWindows before argument len place call data)
    (claims : Claims data.interpretation call) (positive : 0 < len.toNat) :
    ∃ sourcePointer returnPointer,
      argument = .pointer sourcePointer.value ∧
      place.mplace.ptr = returnPointer.value.withOptionalProvenance ∧
      CandidateCallBindings.WindowBinding before sourcePointer.value
        call.sourceId call.sourceOffset call.length ∧
      CandidateCallBindings.WindowBinding before returnPointer.value
        call.returnId call.returnOffset 1 ∧
      UniformOwner (ActualWorld before) held data.interpretation call.sourceOwner
        call.sourceId call.sourceOffset call.length .mut sourcePointer ∧
      UniformOwner (ActualWorld before) held data.interpretation call.returnOwner
        call.returnId call.returnOffset 1 .ret returnPointer := by
  have lengthPositive : 0 < call.length := by rw [actual.2.1]; exact positive
  obtain ⟨sourceLoan,sourcePointer,sourceAllocation,sourcePrecise,sourceLoanAt,
      sourcePointerAt,sourceId,sourcePresent,sourcePreciseAt,sourceRights⟩ :=
    uniform_window _ _ _ joint call.sourceOwner call.sourceId call.sourceOffset call.length
      .mut lengthPositive (fun byte inside => (claims.2.1 byte).mpr inside)
  obtain ⟨returnLoan,returnPointer,returnAllocation,returnPrecise,returnLoanAt,
      returnPointerAt,returnId,returnPresent,returnPreciseAt,returnRights⟩ :=
    uniform_window _ _ _ joint call.returnOwner call.returnId call.returnOffset 1
      .ret (by omega) (fun byte inside => (claims.2.2 byte).mpr inside)
  rcases normalized.1 with empty | ⟨_,bits,argumentEq,boundLoan,boundPointer,
      boundLoanAt,boundPointerAt,valueEq,_,sourceWindow⟩
  · have zero : len = 0 := empty.1
    simp [zero] at positive
  have loanEq : boundLoan = sourceLoan := Option.some.inj (boundLoanAt.symm.trans sourceLoanAt)
  subst boundLoan
  have pointerEq : boundPointer = sourcePointer := Option.some.inj (boundPointerAt.symm.trans sourcePointerAt)
  subst boundPointer
  obtain ⟨_,returnBits,placeEq,boundLoan,boundPointer,boundLoanAt,boundPointerAt,
      returnValueEq,_,returnWindow⟩ := normalized.2
  have loanEq : boundLoan = returnLoan := Option.some.inj (boundLoanAt.symm.trans returnLoanAt)
  subst boundLoan
  have pointerEq : boundPointer = returnPointer := Option.some.inj (boundPointerAt.symm.trans returnPointerAt)
  subst boundPointer
  subst bits
  subst returnBits
  exact ⟨sourcePointer,returnPointer,argumentEq,placeEq,sourceWindow,returnWindow,
    ⟨sourceLoan,sourceAllocation,sourcePrecise,sourceLoanAt,sourcePointerAt,sourceId,
      sourcePresent,sourcePreciseAt,sourceRights⟩,
    ⟨returnLoan,returnAllocation,returnPrecise,returnLoanAt,returnPointerAt,returnId,
      returnPresent,returnPreciseAt,returnRights⟩⟩

end DuplicatePrefix.CandidateCurrentUniformOwnerWindow

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CandidateCurrentUniformOwnerWindow." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved uniform owner window dependency {dependency}"
