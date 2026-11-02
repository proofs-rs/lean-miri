import duplicate_prefix.S05WildcardEntryBridge

namespace DuplicatePrefix.S02WildcardArgumentGeometry
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification
set_option autoImplicit false

/-- The normalized positive wildcard reference names the exact relative
offset used by the typed FnEntry resolver. Its raw inverse-vector geometry
selects either the base-address scope or the interior-window scope. -/
theorem cases {before : Before} (address len : UInt64)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new .wildcard (Size.ofBytes address)) len) :
    reference.offset = address-reference.base ∧
      ((address = reference.base ∧ reference.offset = 0 ∧
        ∃ position, position < before.user.addresses.intToPtrMap.size ∧
          WildcardInteriorHitAddress.Ordered before.user.addresses.intToPtrMap ∧
          before.user.addresses.intToPtrMap[position]? = some ⟨reference.base,reference.id⟩) ∨
       ∃ position, WildcardInteriorHitAddress.Cut before.user.addresses.intToPtrMap address (position+1) ∧
         before.user.addresses.intToPtrMap[position]? = some ⟨reference.base,reference.id⟩ ∧
         address-reference.base < reference.entry.allocation.byteSize.bytes) := by
  have offsetEq : reference.offset = address-reference.base := by
    have addressEq : address = reference.base+reference.offset := reference.pointerAddress
    have shifted := congrArg (fun value : UInt64 => value-reference.base) addressEq
    calc
      reference.offset = (reference.base+reference.offset)-reference.base := by
        rw [UInt64.add_comm,UInt64.add_sub_cancel]
      _ = address-reference.base := shifted.symm
  have binding := reference.binding
  simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at binding
  obtain ⟨_,_,_,geometry⟩ := binding
  refine ⟨offsetEq,?_⟩
  rcases geometry with ⟨same,position,valid,ordered,row⟩ | ⟨position,cut,row,inside⟩
  · change address = reference.base at same
    have shifted := congrArg (fun value : UInt64 => value-reference.base) same
    have zero : reference.offset = 0 := offsetEq.trans (shifted.trans (UInt64.sub_self reference.base))
    exact Or.inl ⟨same,zero,position,valid,ordered,row⟩
  · exact Or.inr ⟨position,cut,row,inside⟩

end DuplicatePrefix.S02WildcardArgumentGeometry

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02WildcardArgumentGeometry.cases) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
