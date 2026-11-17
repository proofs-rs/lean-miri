import Miri.Interpreter.Stack

/-! Frame-local representation lemmas for the actual stack implementation. -/

namespace DuplicatePrefix.FrameFacts
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

theorem replace_value {Prov Layout Extra : Type}
    (frame : Frame Prov Layout Extra) (localId : LocalId) (value : LocalValue Prov)
    (valid : localId < frame.locals.size) :
    frame.replaceLocalValue localId value = .ok
      { frame with locals := (frame.locals.set localId
          { value := value, layout := frame.locals[localId].layout } valid) } := by
  simp [Frame.replaceLocalValue, valid]
  rfl

theorem replace_preserves_shape {Prov Layout Extra : Type}
    (before after : Frame Prov Layout Extra) (localId : LocalId) (value : LocalValue Prov)
    (success : before.replaceLocalValue localId value = .ok after) :
    after.body = before.body ∧ after.bodyIdentity = before.bodyIdentity ∧
      after.functionInstance = before.functionInstance ∧ after.extra = before.extra ∧
      after.location = before.location ∧ after.locals.size = before.locals.size := by
  unfold Frame.replaceLocalValue at success
  split at success
  · simp only [pure, Except.pure, Except.ok.injEq] at success
    subst after
    simp
  · contradiction

theorem get_replaced_value {Prov Layout Extra : Type}
    (before after : Frame Prov Layout Extra) (localId : LocalId) (value : LocalValue Prov)
    (success : before.replaceLocalValue localId value = .ok after) :
    ∃ cached, after.getLocal localId = .ok {value, layout := cached} := by
  unfold Frame.replaceLocalValue at success
  split at success
  · rename_i valid
    simp only [pure, Except.pure, Except.ok.injEq] at success
    subst after
    refine ⟨before.locals[localId].layout, ?_⟩
    simp [Frame.getLocal, valid]
    rfl
  · contradiction

theorem get_other_value {Prov Layout Extra : Type}
    (before after : Frame Prov Layout Extra) (localId other : LocalId) (value : LocalValue Prov)
    (distinct : other ≠ localId)
    (success : before.replaceLocalValue localId value = .ok after) :
    after.getLocal other = before.getLocal other := by
  unfold Frame.replaceLocalValue at success
  split at success
  · simp only [pure, Except.pure, Except.ok.injEq] at success
    subst after
    simp only [Frame.getLocal, Array.size_set]
    split
    · simp [Array.getElem_set, Ne.symm distinct]
    · rfl
  · contradiction

end DuplicatePrefix.FrameFacts
