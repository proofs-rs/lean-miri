import duplicate_prefix.CurrentCallActualReferenceEncoding

/-! Nominal family formation for already-produced current spatial roles.
The operation producer supplies the new value and its rights. This adapter
appends one semantic family identity and one actual occurrence; equal bits
never identify two families. It asserts no retag operation or new authority. -/
namespace DuplicatePrefix.CurrentCallSpatialFamilyFormation
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall
open CurrentCallSpatialCover CurrentCallFamilySatisfaction
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

private theorem optional_represents (value : Pointer Provenance) :
    Represents value.withOptionalProvenance value := by
  simp [Represents,Pointer.withOptionalProvenance]

/-- Apply only to a role whose actual retag construction is already proved.
The actual output role supplies all cell resources unchanged. -/
def append {actual before tracker ctx mode offset length}
    (a : Assignment actual) (produced : RoleCover before tracker ctx mode offset length) :
    Assignment (actual.push produced.family.value.withOptionalProvenance) :=
  a.retag ⟨produced.family.allocation,produced.family.value⟩ produced.family.value.withOptionalProvenance
    (optional_represents produced.family.value)

def role {actual before tracker ctx mode offset length}
    (a : Assignment actual) (produced : RoleCover before tracker ctx mode offset length) :
    RoleCover before tracker ctx mode offset length := reslot_role produced a.families.size

/-- The new nominal identity is internally reserved at the old family-table
end. Its actual value, allocation, and per-cell grants are the producer's. -/
theorem formed {actual before tracker ctx mode offset length}
    (a : Assignment actual) (produced : RoleCover before tracker ctx mode offset length) :
    (append a produced).Binds actual.size (role a produced).family ∧
    (role a produced).family.slot = a.families.size ∧
    (role a produced).family.allocation = produced.family.allocation ∧
    (role a produced).family.value = produced.family.value ∧
    (∀ grant,(role a produced).family.at grant = produced.family.at grant) ∧
    (∀ i overlap,((role a produced).roles i overlap).grant = (produced.roles i overlap).grant) := by
  exact ⟨a.retagged_family _ _ _,rfl,rfl,rfl,fun _ => rfl,fun _ _ => rfl⟩

/-- Every existing bound occurrence, notably the ORIGINAL return destination,
survives source-q and temporary-B family formation unchanged. -/
theorem old_binding {actual before tracker ctx mode offset length occurrence family}
    (a : Assignment actual) (produced : RoleCover before tracker ctx mode offset length)
    (old : a.Binds occurrence family) : (append a produced).Binds occurrence family :=
  a.old_reference_after_retag _ _ _ old

theorem old_family {actual before tracker ctx mode offset length identity payload}
    (a : Assignment actual) (produced : RoleCover before tracker ctx mode offset length)
    (old : a.families[identity]? = some payload) :
    (append a produced).families[identity]? = some payload ∧ identity ≠ (role a produced).family.slot :=
  a.old_family_after_retag _ _ _ old

/-- Even unassigned old occurrences retain their exact table entry. -/
theorem old_reference {actual before tracker ctx mode offset length occurrence}
    (a : Assignment actual) (produced : RoleCover before tracker ctx mode offset length)
    (old : occurrence < actual.size) :
    (append a produced).references[occurrence]? = a.references[occurrence]? := by
  change (a.references.push (some a.families.size))[occurrence]? = a.references[occurrence]?
  rw [Array.getElem?_push,ite_eq_right (show occurrence ≠ a.references.size by rw [a.size];omega)]

/-- Pair this projection with the REAL creator equation/lookup supplied by the
operation producer. The creator's actual pointer is not inferred from bits. -/
theorem actual_output {actual before tracker ctx mode offset length}
    (a : Assignment actual) (produced : RoleCover before tracker ctx mode offset length)
    (actualPointer : Pointer Provenance) (created : produced.family.value = actualPointer) :
    (append a produced).Binds actual.size (role a produced).family ∧
    (role a produced).family.value = actualPointer ∧
    (actual.push produced.family.value.withOptionalProvenance)[actual.size]? =
      some actualPointer.withOptionalProvenance := by
  exact ⟨(formed a produced).1,created,by simp [created]⟩

/-- A plain copy retains its existing semantic ID and table; only an actual
copy equation for the raw value is consumed. -/
theorem plain_copy {actual source returnOccurrence returnFamily}
    (a : Assignment actual) (family : Family) (bound : a.Binds source family)
    (raw : Pointer (Option Provenance)) (copied : actual[source]? = some raw)
    (originalReturn : a.Binds returnOccurrence returnFamily) :
    (a.copy family source bound raw copied).Binds actual.size family ∧
    (a.copy family source bound raw copied).Binds returnOccurrence returnFamily ∧
    (a.copy family source bound raw copied).families = a.families :=
  ⟨a.copied_family family source bound raw copied,
    a.old_reference_after_copy family source bound raw copied originalReturn,rfl⟩


/-- The actual q and temporary Bool roles receive two distinct appended IDs.
The original destination occurrence remains bound to its original family. -/
theorem two_created {actual before tracker sourceCtx boolCtx sourceOffset sourceLength boolOffset returnOccurrence returnFamily}
    (a : Assignment actual)
    (source : RoleCover before tracker sourceCtx .mut sourceOffset sourceLength)
    (temporaryBool : RoleCover before tracker boolCtx .ret boolOffset 1)
    (originalReturn : a.Binds returnOccurrence returnFamily) :
    let sourceAssignment := append a source
    let finalAssignment := append sourceAssignment temporaryBool
    finalAssignment.Binds actual.size (role a source).family ∧
    finalAssignment.Binds (actual.size+1) (role sourceAssignment temporaryBool).family ∧
    finalAssignment.Binds returnOccurrence returnFamily ∧
    (role a source).family.slot = a.families.size ∧
    (role sourceAssignment temporaryBool).family.slot = a.families.size+1 ∧
    (role a source).family.slot ≠ (role sourceAssignment temporaryBool).family.slot := by
  dsimp only
  refine ⟨old_binding (append a source) temporaryBool (formed a source).1,
    by simpa only [Array.size_push] using (formed (append a source) temporaryBool).1,
    old_binding (append a source) temporaryBool (old_binding a source originalReturn),rfl,?_,?_⟩
  · change (a.families.push _).size = a.families.size+1
    exact Array.size_push _
  · change a.families.size ≠ (a.families.push _).size
    rw [Array.size_push]
    omega

end
end DuplicatePrefix.CurrentCallSpatialFamilyFormation
