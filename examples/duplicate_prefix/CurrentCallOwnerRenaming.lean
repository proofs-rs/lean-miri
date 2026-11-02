import duplicate_prefix.CurrentCallResourceNormalization

namespace DuplicatePrefix.CurrentCallOwnerRenaming
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateFreezeContentResources
set_option autoImplicit false

/-- Inject every old owner into the positive owners, including an infinite
suspended support. Pointer and family indices are a separate namespace. -/
def shiftContent (F : Fragment) : Fragment
  | _, 0 => none
  | byte, n + 1 => F byte n

@[simp] theorem shiftContent_zero (F : Fragment) (byte : Byte) : shiftContent F byte 0 = none := rfl
@[simp] theorem shiftContent_succ (F : Fragment) (byte : Byte) (owner : Nat) :
    shiftContent F byte (owner + 1) = F byte owner := rfl

theorem shiftContent_valid {F : Fragment} (valid : Valid F) : Valid (shiftContent F) := by
  intro byte first second fc sc ne hf hs
  cases first with
  | zero => simp at hf
  | succ first =>
    cases second with
    | zero => simp at hs
    | succ second => exact valid byte first second fc sc (fun eq => ne (congrArg Nat.succ eq)) hf hs

def shiftLoan (loan : Loan) : Loan := { loan with parent := loan.parent.map Nat.succ }

/-- The uncharged reserved slot has a root loan at an already present pointer.
Its pointer existence is justified independently; no content is minted. -/
def shiftInterpretation (I : Interpretation) (pointerSlot : Nat) : Interpretation :=
  { precise := I.precise
    pointers := I.pointers
    loans := #[⟨pointerSlot, none, 0⟩] ++ I.loans.map shiftLoan
    content := shiftContent I.content }

def shiftCall (call : CallLoans) : CallLoans :=
  { call with sourceOwner := call.sourceOwner + 1, returnOwner := call.returnOwner + 1 }

@[simp] theorem shifted_loan_zero (I : Interpretation) (slot : Nat) :
    (shiftInterpretation I slot).loans[0]? = some ⟨slot, none, 0⟩ := by
  simp [shiftInterpretation, Array.getElem?_append]

@[simp] theorem shifted_loan_succ (I : Interpretation) (slot owner : Nat) :
    (shiftInterpretation I slot).loans[owner + 1]? = (I.loans[owner]?).map shiftLoan := by
  simp [shiftInterpretation, Array.getElem?_append]

theorem shift_claims {I : Interpretation} {call : CallLoans} (claims : Claims I call) (slot : Nat) :
    Claims (shiftInterpretation I slot) (shiftCall call) := by
  exact ⟨fun eq => claims.1 (Nat.succ.inj eq), claims.2.1, claims.2.2⟩

/-- All old active and suspended resources survive simultaneously, together
with every parent-loan link. No finiteness assumption on content is needed. -/
theorem shift_joint {world : World} {held : Miri.TreeBorrows.ProtectedTags}
    {I : Interpretation} (joint : PreciseJoint world held I)
    (slot : Nat) (pointer : PointerInstance) (pointerAt : I.pointers[slot]? = some pointer) :
    PreciseJoint world held (shiftInterpretation I slot) := by
  refine ⟨joint.1, shiftContent_valid joint.2.1, ?_, ?_⟩
  · intro owner loan loanAt
    cases owner with
    | zero =>
      have eq := Option.some.inj ((shifted_loan_zero I slot).symm.trans loanAt)
      subst loan
      exact ⟨⟨pointer,pointerAt⟩, by intro parent h; cases h⟩
    | succ owner =>
      rw [shifted_loan_succ] at loanAt
      obtain ⟨old, oldAt, eq⟩ := Option.map_eq_some_iff.mp loanAt
      subst loan
      obtain ⟨pointers, parents⟩ := joint.2.2.1 owner old oldAt
      refine ⟨pointers, ?_⟩
      intro parent parentAt
      obtain ⟨oldParent, oldParentAt, eq⟩ := Option.map_eq_some_iff.mp parentAt
      subst parent
      obtain ⟨earlier, earlierAt, depth⟩ := parents oldParent oldParentAt
      exact ⟨shiftLoan earlier, by simp [earlierAt], depth⟩
  · intro byte owner charge contentAt
    cases owner with
    | zero => simp [shiftInterpretation] at contentAt
    | succ owner =>
      obtain ⟨loan,pointer,allocation,precise,loanAt,pointerAt,id,present,bound,preciseAt,rights,parents⟩ :=
        joint.2.2.2 byte owner charge contentAt
      refine ⟨shiftLoan loan,pointer,allocation,precise,by simp [loanAt],pointerAt,id,present,bound,preciseAt,rights,?_⟩
      intro parent parentAt
      obtain ⟨oldParent, oldParentAt, eq⟩ := Option.map_eq_some_iff.mp parentAt
      subst parent
      obtain ⟨parentLoan,parentPointer,parentCharge,parentLoanAt,parentPointerAt,parentId,below,parentContent,suspended,delegates⟩ := parents oldParent oldParentAt
      exact ⟨shiftLoan parentLoan,parentPointer,parentCharge,by simp [parentLoanAt],parentPointerAt,parentId,below,parentContent,suspended,delegates⟩


/-- A call's existing one-byte return claim supplies the filler pointer. Thus
joint call renaming introduces no new caller-side existence assumption. -/
theorem shift_joint_claims {world : World} {held : Miri.TreeBorrows.ProtectedTags}
    {I : Interpretation} {call : CallLoans} (joint : PreciseJoint world held I)
    (claims : Claims I call) :
    ∃ slot, PreciseJoint world held (shiftInterpretation I slot) ∧
      Claims (shiftInterpretation I slot) (shiftCall call) := by
  have window : Window call.returnId call.returnOffset 1 (call.returnId,call.returnOffset) :=
    ⟨rfl,Nat.le_refl _,by omega⟩
  obtain ⟨loan,pointer,_,_,_,pointerAt,_⟩ :=
    joint.2.2.2 _ call.returnOwner _ ((claims.2.2 _).mpr window)
  exact ⟨loan.pointer,shift_joint joint loan.pointer pointer pointerAt,shift_claims claims loan.pointer⟩


def shiftData (data : Identities) (slot : Nat) : Identities :=
  { data with interpretation := shiftInterpretation data.interpretation slot }

theorem shift_ownerBinding {before I owner pointer id offset length}
    (binding : CandidateCallBindings.OwnerBinding before I owner pointer id offset length) (slot : Nat) :
    CandidateCallBindings.OwnerBinding before (shiftInterpretation I slot) (owner + 1)
      pointer id offset length := by
  obtain ⟨loan,ptrInstance,loanAt,instanceAt,value,allocation,window⟩ := binding
  exact ⟨shiftLoan loan,ptrInstance,by simp [loanAt],instanceAt,value,allocation,window⟩

/-- The current denotation checks active resources only. Its transport is
unconditional even when suspended content occupies every old owner. All listed
actual pointer occurrences and attachments retain their original family slots. -/
theorem shift_denotation {before tracker argument len place call data}
    (D : CurrentCallResourceNormalization.CurrentDenotation before tracker argument len place call data)
    (slot : Nat) :
    CurrentCallResourceNormalization.CurrentDenotation before tracker argument len place
      (shiftCall call) (shiftData data slot) := by
  refine ⟨D.worldIds,D.interpretationIds,D.length,shift_claims D.claims slot,
    D.listedCopies,shiftContent_valid D.contents,?_,?_,D.sourceStorage,D.returnStorage,?_⟩
  · rcases D.sourceBinding with empty | ⟨nonempty,pointer,argumentEq,binding⟩
    · exact .inl empty
    · exact .inr ⟨nonempty,pointer,argumentEq,shift_ownerBinding binding slot⟩
  · obtain ⟨layout,pointer,placeEq,binding⟩ := D.returnBinding
    exact ⟨layout,pointer,placeEq,shift_ownerBinding binding slot⟩
  · intro byte owner mode active
    cases owner with
    | zero => cases active
    | succ owner =>
      obtain ⟨loan,pointer,allocation,precise,loanAt,pointerAt,allocationId,present,bound,
        preciseAt,parents,binding,issued,embeds⟩ := D.active byte owner mode active
      exact ⟨shiftLoan loan,pointer,allocation,precise,by simp [shiftData,loanAt],
        pointerAt,allocationId,present,bound,preciseAt,parents,binding,issued,embeds⟩

end DuplicatePrefix.CurrentCallOwnerRenaming
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallOwnerRenaming.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved owner renaming dependency {dependency}"
