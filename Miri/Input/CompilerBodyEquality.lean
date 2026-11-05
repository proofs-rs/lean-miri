import Miri.MIR.Syntax

/-! Avoid repeated structural comparisons when a frame retains the canonical
MIR body object. Pointer equality is only a sufficient fast path: every other
pair uses the original complete structural comparison. -/
namespace Miri.Input

@[inline] abbrev bodyContentsEqual (a b : MIR.Body) : Bool :=
  withPtrEq a b (fun _ => a == b) (by intro same; subst b; exact beq_self_eq_true a)

@[simp] theorem bodyContentsEqual_eq (a b : MIR.Body) : bodyContentsEqual a b = (a == b) := rfl

end Miri.Input
