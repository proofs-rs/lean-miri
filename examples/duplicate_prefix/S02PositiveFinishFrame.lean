import duplicate_prefix.PositiveRootArguments
import duplicate_prefix.RootArgumentsTwo
import duplicate_prefix.RawRootInvocation

namespace DuplicatePrefix.S02PositiveFinishFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open RootFrameData EmptyRootArguments PositiveRootArguments
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Positive argument setup changes locals 1 and 2 only. -/
theorem untouched (root : RootFrame) (adjusted : Immediate Provenance)
    (borrowFrame : FrameState) (allocation : AllocId) (tag : BorTag)
    (count : UInt64) (i : Fin 25) (ne1 : i.val ≠ 1) (ne2 : i.val ≠ 2) :
    ((RootArgumentsTwo.result (PositiveRootArguments.firstDone root adjusted borrowFrame allocation tag) count).frame.locals[i.val]'
      ((RootArgumentsTwo.result (PositiveRootArguments.firstDone root adjusted borrowFrame allocation tag) count).valid i)).value =
      (root.frame.locals[i.val]'(root.valid i)).value := by
  simp only [RootArgumentsTwo.result,PositiveRootArguments.firstDone,PositiveRootArguments.protectedRoot,
    TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,
    firstLive,firstCache,live,write,cache,atSpan,LocalOperands.cachedLayoutFrame,i1,i2,
    Array.getElem_set,ne1,ne2,Ne.symm ne1,Ne.symm ne2,
    show ¬(1:Nat)=2 by decide,show ¬(2:Nat)=1 by decide,
    eq_self_iff_true,ite_true,ite_false,root.size]

/-- The frame shape required by `RootEntryFinish.actual_finish` survives
the return protector's frame update. The theorem is structural: it neither
assumes nor proves success of the destination memory/borrow operation. -/
theorem after_destination_registration (root : RootFrame)
    (raw : root.frame.locals = Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (adjusted : Immediate Provenance) (count : UInt64)
    (argumentId destinationId : AllocId) (argumentTag destinationTag : BorTag) :
    let args := RootArgumentsTwo.result
      (PositiveRootArguments.firstDone root adjusted ({} : FrameState) argumentId argumentTag) count
    let owned := ({} : FrameState).addProtector argumentId argumentTag
    let protectedFrame := TypedBorrowSteps.registeredFrame
      {args.frame with location := .unwinding ⟨601⟩} owned destinationId destinationTag
    protectedFrame.body = RootBody.reflected.body.body ∧
    protectedFrame.locals.size = 25 ∧
    (∀ (i : Fin 25) (valid : i.val < protectedFrame.locals.size),
      (i.val = 0 ∨ i.val = 6 ∨ i.val = 13 ∨ i.val = 14) →
      (protectedFrame.locals[i.val]'valid).value = .dead) ∧
    protectedFrame.extra.dataRace = none := by
  let args := RootArgumentsTwo.result
    (PositiveRootArguments.firstDone root adjusted ({} : FrameState) argumentId argumentTag) count
  let owned := ({} : FrameState).addProtector argumentId argumentTag
  let protectedFrame := TypedBorrowSteps.registeredFrame
    {args.frame with location := .unwinding ⟨601⟩} owned destinationId destinationTag
  have read (i : Fin 25) (ne1 : i.val ≠ 1) (ne2 : i.val ≠ 2) :
      (args.frame.locals[i.val]'(args.valid i)).value = .dead := by
    rw [untouched root adjusted {} argumentId argumentTag count i ne1 ne2]
    have row := congrArg (fun rows : Array (LocalState Provenance LocalLayout) => rows[i.val]?) raw
    have equal : root.frame.locals[i.val]? = some (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
      simpa only [Array.getElem?_replicate,i.isLt,↓reduceIte] using row
    have exactRow := Option.some.inj ((Array.getElem?_eq_getElem (root.valid i)).symm.trans equal)
    rw [exactRow]
  refine ⟨?_,?_,?_,?_⟩
  · exact args.body
  · exact args.size
  · intro i valid member
    have ne1 : i.val ≠ 1 := by rcases member with h | h | h | h <;> omega
    have ne2 : i.val ≠ 2 := by rcases member with h | h | h | h <;> omega
    exact read i ne1 ne2
  · exact args.noClocks

end
end DuplicatePrefix.S02PositiveFinishFrame
