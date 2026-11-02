import duplicate_prefix.S02WildcardArgumentGeometry
import duplicate_prefix.WildcardOrderedHitAddress
import duplicate_prefix.WildcardInteriorHitAddress

namespace DuplicatePrefix.S02WildcardPositiveIdUnique
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification
set_option autoImplicit false
noncomputable section

/-- Two normalized positive references to the same wildcard address resolve to
one inverse-map row, including exact-base and interior cases. -/
theorem same_id {before : Before} (address len : UInt64)
    (first second : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new .wildcard (Size.ofBytes address)) len) : first.id = second.id := by
  let entries := before.user.addresses.intToPtrMap
  have firstGeometry := (S02WildcardArgumentGeometry.cases address len first).2
  have secondGeometry := (S02WildcardArgumentGeometry.cases address len second).2
  rcases firstGeometry with ⟨same1,_,p,hp,ordered,row1⟩ | ⟨p,cut1,row1,_⟩
  · rcases secondGeometry with ⟨same2,_,q,hq,_ordered2,row2⟩ | ⟨q,cut2,row2,_⟩
    · have search1 := WildcardOrderedHitAddress.inverse_hit entries address first.id p hp ordered
        (by simpa only [entries,same1] using row1)
      have search2 := WildcardOrderedHitAddress.inverse_hit entries address second.id q hq ordered
        (by simpa only [entries,same2] using row2)
      have pos : p = q := by
        have h := search1.symm.trans search2
        exact congrArg Prod.fst h
      subst q
      have sameRow : (⟨first.base,first.id⟩ : InverseAddressEntry) = ⟨second.base,second.id⟩ :=
        Option.some.inj (row1.symm.trans row2)
      exact congrArg InverseAddressEntry.allocId sameRow
    · have search1 := WildcardOrderedHitAddress.inverse_hit entries address first.id p hp ordered
        (by simpa only [entries,same1] using row1)
      have search2 := WildcardInteriorHitAddress.inverse_cut entries address (q+1) cut2
      have impossible := search1.symm.trans search2
      cases impossible
  · rcases secondGeometry with ⟨same2,_,q,hq,ordered,row2⟩ | ⟨q,cut2,row2,_⟩
    · have search1 := WildcardInteriorHitAddress.inverse_cut entries address (p+1) cut1
      have search2 := WildcardOrderedHitAddress.inverse_hit entries address second.id q hq ordered
        (by simpa only [entries,same2] using row2)
      have impossible := search1.symm.trans search2
      cases impossible
    · have search1 := WildcardInteriorHitAddress.inverse_cut entries address (p+1) cut1
      have search2 := WildcardInteriorHitAddress.inverse_cut entries address (q+1) cut2
      have pos : p = q := by
        have h := congrArg Prod.fst (search1.symm.trans search2)
        omega
      subst q
      have sameRow : (⟨first.base,first.id⟩ : InverseAddressEntry) = ⟨second.base,second.id⟩ :=
        Option.some.inj (row1.symm.trans row2)
      exact congrArg InverseAddressEntry.allocId sameRow

end
end DuplicatePrefix.S02WildcardPositiveIdUnique

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardPositiveIdUnique.same_id) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard positive ID-uniqueness dependency {dependency}"
