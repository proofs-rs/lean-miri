import duplicate_prefix.CurrentCallSourceHandoff
import duplicate_prefix.CurrentCallResourceFnEntry

namespace DuplicatePrefix.CurrentCallSourceHandoffAdequacy
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization
set_option autoImplicit false

/-- One charged byte realized in the actual post heap. The completion is
explicit and need not be the unchanged bookkeeping array's old completion. -/
def ActiveAt (post : Before) (next : MachineHooks.BorrowState) (data : Identities)
    (owner : Nat) (byte : CandidateFreezeContentResources.Byte)
    (mode : CandidateFreezeContentResources.Mode) : Prop :=
  ∃ loan pointer allocation completion,
    data.interpretation.loans[owner]? = some loan ∧
    data.interpretation.pointers[loan.pointer]? = some pointer ∧
    pointer.allocation = byte.1 ∧ Present (ActualWorld post) byte.1 allocation ∧ byte.2 < allocation.len ∧
    ParentInterpretation allocation.extra completion ∧ PointerBinds allocation pointer ∧
    SpatialDelegation post next byte.1 allocation completion pointer.grant ∧
    Embeds allocation next.global.protectedTags completion pointer.grant byte.2 (demandOf mode)

/-- The SAME actual borrow witness realizes owner0 after exact source handoff.
Only actual installed presence and the spatial issuance already derived by
BorrowIssuance.post are consumed. No pre-state denotation is assigned to a
changed allocation and no whole post denotation is asserted. -/
theorem source_active {before tracker data} {call : CallLoans}
    (W : UniformWindow before tracker data call.sourceOwner call.sourceId call.sourceOffset call.length .mut)
    (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex) (start amount : UInt64)
    (witness : CurrentCallResourceFnEntry.BorrowWitness W output child start amount)
    (post : Before)
    (present : Present (ActualWorld post) call.sourceId (W.allocation.setExtra output.child.tree))
    (issued : SpatialDelegation post ⟨output.global,tracker.retagMode⟩ call.sourceId
      (W.allocation.setExtra output.child.tree)
      (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) child)
    (byte : CandidateFreezeContentResources.Byte)
    (active : (CurrentCallSourceHandoff.install data call.sourceOwner W.loan
      (CurrentCallResourceFnEntry.child_pointer W output.tag child)
      (Window call.sourceId call.sourceOffset call.length)).interpretation.content byte 0 = some ⟨.mut,.active⟩) :
    ActiveAt post ⟨output.global,tracker.retagMode⟩
      (CurrentCallSourceHandoff.install data call.sourceOwner W.loan
        (CurrentCallResourceFnEntry.child_pointer W output.tag child)
        (Window call.sourceId call.sourceOffset call.length)) 0 byte .mut := by
  classical
  have inside : Window call.sourceId call.sourceOffset call.length byte := by
    change (if Window call.sourceId call.sourceOffset call.length byte then
      some (⟨.mut,.active⟩ : CandidateFreezeContentResources.Charge) else none) = _ at active
    split at active
    · assumption
    · cases active
  obtain ⟨bound,embeds⟩ := witness.window byte inside
  have id : byte.1 = call.sourceId := inside.1
  refine ⟨⟨data.interpretation.pointers.size,some (call.sourceOwner + 1),W.loan.depth + 1⟩,
    CurrentCallResourceFnEntry.child_pointer W output.tag child,
    W.allocation.setExtra output.child.tree,
    S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant,
    CurrentCallSourceHandoff.child_loan _ _ _ _ _,CurrentCallSourceHandoff.child_pointer _ _ _ _ _,
    id.symm,?_,bound,witness.parents,witness.binding,?_,embeds⟩
  · simpa only [id] using present
  · simpa only [id,CurrentCallResourceFnEntry.child_pointer] using issued

/-- Immediate consumer of the initial denotation and ONE actual source borrow:
valid exact resources, stable old identities, the linked old parent family,
and realized fresh active bytes are established together. -/
theorem source_handoff {before tracker data argument len place} {call : CallLoans}
    (D : CurrentDenotation before tracker argument len place call data)
    (W : UniformWindow before tracker data call.sourceOwner call.sourceId call.sourceOffset call.length .mut)
    (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex) (start amount : UInt64)
    (witness : CurrentCallResourceFnEntry.BorrowWitness W output child start amount)
    (post : Before)
    (present : Present (ActualWorld post) call.sourceId (W.allocation.setExtra output.child.tree))
    (issued : SpatialDelegation post ⟨output.global,tracker.retagMode⟩ call.sourceId
      (W.allocation.setExtra output.child.tree)
      (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) child) :
    let installed := CurrentCallSourceHandoff.install data call.sourceOwner W.loan
      (CurrentCallResourceFnEntry.child_pointer W output.tag child)
      (Window call.sourceId call.sourceOffset call.length)
    CandidateFreezeContentResources.Valid installed.interpretation.content ∧
    Claims installed.interpretation (CurrentCallSourceHandoff.childCall call) ∧
    StableChoices installed ∧
    installed.interpretation.pointers[W.loan.pointer]? = some W.pointer ∧
    installed.interpretation.loans[call.sourceOwner + 1]? = some (CurrentCallOwnerRenaming.shiftLoan W.loan) ∧
    (∀ byte, installed.interpretation.content byte 0 = some ⟨.mut,.active⟩ →
      ActiveAt post ⟨output.global,tracker.retagMode⟩ installed 0 byte .mut) := by
  obtain ⟨valid,claims⟩ := CurrentCallSourceHandoff.call_handoff D.contents D.claims W.loan
    (CurrentCallResourceFnEntry.child_pointer W output.tag child)
  exact ⟨valid,claims,CurrentCallSourceHandoff.stableChoices D.listedCopies _ _ _ _,
    CurrentCallSourceHandoff.old_pointer _ _ _ _ witness.parentFamilyAt,
    CurrentCallSourceHandoff.parent_loan _ _ _ _ witness.parentLoanAt,
    source_active W output child start amount witness post present issued⟩

/-- Exact source handoff preserves the old Bool family's indices and content.
Its raw realization comes from the supplied transported post-role fields,
including the actual post allocation and completion. -/
theorem return_active {before tracker data post next} {call : CallLoans}
    (claims : Claims data.interpretation call)
    (V : UniformWindow before tracker data call.returnOwner call.returnId call.returnOffset 1 .ret)
    (sourceParent : Loan) (sourceChild : PointerInstance)
    (tree : BorrowTree) (completion : Completion)
    (present : Present (ActualWorld post) call.returnId (V.allocation.setExtra tree))
    (parents : ParentInterpretation tree completion)
    (binding : PointerBinds (V.allocation.setExtra tree) V.pointer)
    (issued : SpatialDelegation post next call.returnId (V.allocation.setExtra tree) completion V.pointer.grant)
    (window : ∀ byte, Window call.returnId call.returnOffset 1 byte → byte.2 < V.allocation.len ∧
      Embeds (V.allocation.setExtra tree) next.global.protectedTags completion V.pointer.grant byte.2 .exclusive)
    (byte : CandidateFreezeContentResources.Byte)
    (active : (CurrentCallSourceHandoff.install data call.sourceOwner sourceParent sourceChild
      (Window call.sourceId call.sourceOffset call.length)).interpretation.content byte (call.returnOwner + 1) = some ⟨.ret,.active⟩) :
    ActiveAt post next
      (CurrentCallSourceHandoff.install data call.sourceOwner sourceParent sourceChild
        (Window call.sourceId call.sourceOffset call.length)) (call.returnOwner + 1) byte .ret := by
  have oldActive : data.interpretation.content byte call.returnOwner = some ⟨.ret,.active⟩ := by
    exact (CurrentCallSourceHandoff.other_content _ _ _ _ _ (Ne.symm claims.1)).symm.trans active
  have inside := (claims.2.2 byte).mp oldActive
  obtain ⟨bound,embeds⟩ := window byte inside
  have id : byte.1 = call.returnId := inside.1
  refine ⟨CurrentCallOwnerRenaming.shiftLoan V.loan,V.pointer,V.allocation.setExtra tree,completion,
    ?_,?_,V.pointerId.trans id.symm,?_,bound,parents,binding,?_,embeds⟩
  · simp [V.loanAt]
  · exact CurrentCallSourceHandoff.old_pointer _ _ _ _ V.pointerAt
  · simpa only [id] using present
  · simpa only [id,CurrentCallResourceFnEntry.child_pointer] using issued

end DuplicatePrefix.CurrentCallSourceHandoffAdequacy
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallSourceHandoffAdequacy.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved source handoff adequacy dependency {dependency}"
